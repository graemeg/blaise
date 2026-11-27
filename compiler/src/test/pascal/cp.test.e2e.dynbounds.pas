{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.dynbounds;

{ Dynamic-array indices are bounds-checked at run time, in every build
  (BUG-20261027-dynarray-no-bounds-check; docs/language-rationale.adoc,
  "Dynamic Array Indices Are Always Bounds-Checked").  An index outside
  0..High raises ERangeError when SysUtils is linked, and is a fatal runtime
  error with exit code 201 when it is not.  The check is an inline compare
  against the length header: the in-process harness pins that it is
  emitted (cp.test.rterrorhooks), and these tests that it fires on every
  access path and every index kind, and that in-range accesses still work. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EDynBoundsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { read, write, nil array, var argument, Inc, record-element field,
      record dyn-array field, multi-dimensional (both levels), Self field,
      var-param array, captured array -- each caught as ERangeError }
    procedure TestRun_EveryAccessPath_RaisesERangeError;
    { every index integer kind and an enum at its boundaries (Length-1
      passes, Length fails, Low/High of the kind fail), float, string and
      interface elements, and the address of an element }
    procedure TestRun_IndexKinds_Boundaries;
    { an array captured by a closure that outlives its routine }
    procedure TestRun_ClosureCapture_RaisesERangeError;
    { the shapes the first pass left untested: an owned call-result base,
      interface / float / record elements of a field array, a record-call
      right-hand side, a field chain, closure and jumbo-set elements, and
      the address of element 0 of an empty array }
    procedure TestRun_MoreShapes_RaiseERangeError;
    { A[I] := F() with I out of range raises before F runs, on every ISA
      and element kind: x86-64 evaluated the value first, so F ran and an
      owned result it returned leaked when the check raised }
    procedure TestRun_BadIndexWrite_ValueNotEvaluated;
    { Pointer(A) on a dynamic array is its data pointer, nil when empty,
      and never checked }
    procedure TestRun_PointerOfDynArray;
    { A[I] := V where evaluating V resizes A: the store lands in the
      array as it is after V, never in the block V freed (arm64 parked the
      element address before evaluating V) }
    procedure TestRun_ValueResizesTheArray;
    { each part of an element write is evaluated once: the receiver of a
      field array (MakeObj().Arr[I]), the index; a value that SHRINKS the
      array fails the check after it; the chained pin holds for an
      interface-method and a getter-property value }
    procedure TestRun_EvaluatedOnce_Shrink_GetterPins;
    { left to right: the array (receiver), then the index, then the value,
      for reads and writes, on every ISA }
    procedure TestRun_LeftToRight_ArrayIndexValue;
    { an owned value whose evaluation shrinks the array so the check after
      it raises is released, not leaked }
    procedure TestDebug_ShrinkingValue_NoLeak;
    { an index or value that drops what the statement is reading or writing
      through: a string reassigned by the index, a receiver object freed by
      the value -- read or written safely, nothing leaked; left to right
      for interface, float and Inc element forms }
    procedure TestDebug_IndexOrValueDropsTheBase_NoLeak;
    { the remaining shapes: a field-array read and a static array inside a
      dynamic one whose index resizes the array, a string-field byte write,
      a PChar write and a static-array field write -- left to right, and
      never through a freed block }
    procedure TestDebug_RemainingShapes_LeftToRight_NoLeak;
    { a value that changes a call-free index (a global) or reassigns the
      pointer being written: the index is read before the value, a named
      pointer after it -- the same element on every ISA }
    procedure TestRun_ValueChangesIndexOrPointer;
    { a string byte write whose string is reached through a call is left to
      right; an owned value is released when the value shrinks the array
      that holds the target, so locating it again raises }
    procedure TestDebug_StringElemOrder_RelocationRaise_NoLeak;
    { the report's program without SysUtils: the diagnostic and exit code
      201 after the last good access }
    procedure TestRun_NoSysUtils_ExitCode201;
  end;

implementation

const
  LE = #10;

procedure TE2EDynBoundsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-dynbounds');
end;

procedure TE2EDynBoundsTests.TestRun_EveryAccessPath_RaisesERangeError;
const
  Src = '''
    program DynBoundsCatch;
    uses SysUtils;
    type
      TRec = record
        F: Int;
        S: string;
      end;
      THolder = record
        Arr: array of Int;
      end;
      TBox = class
        FArr: array of Int;
        procedure Probe(I: Int);
      end;
      TIntArr = array of Int;
    var
      A: array of Int;
      N: array of Int;
      R: array of TRec;
      H: THolder;
      M: array of array of Int;
      Box: TBox;
      I, X: Int;

    procedure Bump(var V: Int);
    begin
      V := V + 1
    end;

    procedure TBox.Probe(I: Int);
    begin
      try
        FArr[I] := 1;
        WriteLn('miss self-write')
      except
        on E: ERangeError do WriteLn('self-write')
      end;
      try
        X := FArr[I];
        WriteLn('miss self-read')
      except
        on E: ERangeError do WriteLn('self-read')
      end
    end;

    procedure ByVar(var V: TIntArr; I: Int);
    begin
      try
        V[I] := 1;
        WriteLn('miss var-write')
      except
        on E: ERangeError do WriteLn('var-write')
      end;
      try
        X := V[I];
        WriteLn('miss var-read')
      except
        on E: ERangeError do WriteLn('var-read')
      end
    end;

    procedure Captured;
    var
      L: array of Int;
      procedure Inner(I: Int);
      begin
        try
          L[I] := 1;
          WriteLn('miss cap-write')
        except
          on E: ERangeError do WriteLn('cap-write')
        end;
        try
          X := L[I];
          WriteLn('miss cap-read')
        except
          on E: ERangeError do WriteLn('cap-read')
        end;
        L[I - 1] := 7;
        WriteLn('cap-ok ', L[I - 1])
      end;
    begin
      SetLength(L, 2);
      Inner(2)
    end;

    begin
      SetLength(A, 4);
      for I := 0 to 3 do A[I] := I * 10;
      I := 4;
      try
        X := A[I];
        WriteLn('miss read-high')
      except
        on E: ERangeError do WriteLn('read-high: ', E.Message)
      end;
      I := -1;
      try
        X := A[I];
        WriteLn('miss read-neg')
      except
        on E: ERangeError do WriteLn('read-neg')
      end;
      try
        A[4] := 1;
        WriteLn('miss write-high')
      except
        on E: ERangeError do WriteLn('write-high')
      end;
      try
        A[-1] := 1;
        WriteLn('miss write-neg')
      except
        on E: ERangeError do WriteLn('write-neg')
      end;
      try
        X := N[0];
        WriteLn('miss nil-read')
      except
        on E: ERangeError do WriteLn('nil-read')
      end;
      try
        N[0] := 1;
        WriteLn('miss nil-write')
      except
        on E: ERangeError do WriteLn('nil-write')
      end;
      try
        Bump(A[4]);
        WriteLn('miss var-arg')
      except
        on E: ERangeError do WriteLn('var-arg')
      end;
      try
        Inc(A[4]);
        WriteLn('miss inc')
      except
        on E: ERangeError do WriteLn('inc')
      end;
      SetLength(R, 2);
      try
        R[2].F := 1;
        WriteLn('miss rec-field-write')
      except
        on E: ERangeError do WriteLn('rec-field-write')
      end;
      try
        X := R[2].F;
        WriteLn('miss rec-field-read')
      except
        on E: ERangeError do WriteLn('rec-field-read')
      end;
      try
        R[2].S := 'x';
        WriteLn('miss rec-str-write')
      except
        on E: ERangeError do WriteLn('rec-str-write')
      end;
      SetLength(H.Arr, 3);
      try
        H.Arr[3] := 1;
        WriteLn('miss field-write')
      except
        on E: ERangeError do WriteLn('field-write')
      end;
      try
        X := H.Arr[3];
        WriteLn('miss field-read')
      except
        on E: ERangeError do WriteLn('field-read')
      end;
      SetLength(M, 2);
      SetLength(M[0], 2);
      SetLength(M[1], 2);
      try
        X := M[1, 2];
        WriteLn('miss md-read-inner')
      except
        on E: ERangeError do WriteLn('md-read-inner')
      end;
      try
        X := M[2][0];
        WriteLn('miss md-read-outer')
      except
        on E: ERangeError do WriteLn('md-read-outer')
      end;
      try
        M[1][2] := 1;
        WriteLn('miss md-write-inner')
      except
        on E: ERangeError do WriteLn('md-write-inner')
      end;
      try
        M[2][0] := 1;
        WriteLn('miss md-write-outer')
      except
        on E: ERangeError do WriteLn('md-write-outer')
      end;
      try
        X := High(M[2]);
        WriteLn('miss md-high')
      except
        on E: ERangeError do WriteLn('md-high')
      end;
      Box := TBox.Create();
      SetLength(Box.FArr, 1);
      Box.Probe(1);
      ByVar(A, 4);
      Captured();
      { in range: every path still works }
      A[3] := 33;
      Bump(A[3]);
      Inc(A[0]);
      R[1].F := 5;
      R[1].S := 'ok';
      H.Arr[2] := 9;
      M[1, 1] := 11;
      Box.FArr[0] := 2;
      WriteLn(A[0], ' ', A[3], ' ', R[1].F, ' ', R[1].S, ' ', H.Arr[2], ' ',
        M[1][1], ' ', Box.FArr[0], ' ', Length(A), ' ', High(M[1]));
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(Src,
    'read-high: Range check error' + LE +
    'read-neg' + LE +
    'write-high' + LE +
    'write-neg' + LE +
    'nil-read' + LE +
    'nil-write' + LE +
    'var-arg' + LE +
    'inc' + LE +
    'rec-field-write' + LE +
    'rec-field-read' + LE +
    'rec-str-write' + LE +
    'field-write' + LE +
    'field-read' + LE +
    'md-read-inner' + LE +
    'md-read-outer' + LE +
    'md-write-inner' + LE +
    'md-write-outer' + LE +
    'md-high' + LE +
    'self-write' + LE +
    'self-read' + LE +
    'var-write' + LE +
    'var-read' + LE +
    'cap-write' + LE +
    'cap-read' + LE +
    'cap-ok 7' + LE +
    '1 34 5 ok 9 11 2 4 1' + LE +
    'done' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_IndexKinds_Boundaries;
const
  { 26 out-of-range accesses, each must be caught }
  Src = '''
    program DynBoundsKinds;
    uses SysUtils;
    type
      TColor = (cRed, cGreen, cBlue);
      IThing = interface
        function Id: Int;
      end;
      TThing = class(IThing)
        function Id: Int;
      end;
    var
      A: array of Int;
      D: array of Float64;
      S: array of string;
      T: array of IThing;
      B: UInt8;
      I8: Int8;
      W: UInt16;
      I16: Int16;
      I32: Int32;
      U32: UInt32;
      I64: Int64;
      U64: UInt64;
      C: TColor;
      P: ^Int;
      X: Int;
      Hits: Int;

    function TThing.Id: Int;
    begin
      Result := 42
    end;

    procedure Hit(const AName: string);
    begin
      Hits := Hits + 1
    end;

    begin
      Hits := 0;
      { Byte: Length 255, so 254 is the last element and 255 is out }
      SetLength(A, 255);
      B := 254;
      A[B] := 1;
      B := 255;
      try X := A[B]; WriteLn('miss byte-high') except on E: ERangeError do Hit('b') end;
      try A[B] := 1; WriteLn('miss byte-high-w') except on E: ERangeError do Hit('b') end;
      { Int8 }
      SetLength(A, 127);
      I8 := 126;
      A[I8] := 1;
      I8 := High(Int8);
      try X := A[I8]; WriteLn('miss i8-high') except on E: ERangeError do Hit('i8') end;
      I8 := Low(Int8);
      try X := A[I8]; WriteLn('miss i8-low') except on E: ERangeError do Hit('i8') end;
      I8 := -1;
      try A[I8] := 1; WriteLn('miss i8-neg') except on E: ERangeError do Hit('i8') end;
      { UInt16: Length 65535 }
      SetLength(A, 65535);
      W := 65534;
      A[W] := 1;
      W := High(UInt16);
      try X := A[W]; WriteLn('miss word-high') except on E: ERangeError do Hit('w') end;
      { Int16 }
      SetLength(A, 100);
      I16 := 99;
      A[I16] := 1;
      I16 := High(Int16);
      try X := A[I16]; WriteLn('miss i16-high') except on E: ERangeError do Hit('i16') end;
      I16 := Low(Int16);
      try X := A[I16]; WriteLn('miss i16-low') except on E: ERangeError do Hit('i16') end;
      { Integer }
      I32 := 99;
      A[I32] := 1;
      I32 := 100;
      try X := A[I32]; WriteLn('miss i32-len') except on E: ERangeError do Hit('i32') end;
      I32 := High(Int32);
      try X := A[I32]; WriteLn('miss i32-high') except on E: ERangeError do Hit('i32') end;
      I32 := Low(Int32);
      try A[I32] := 1; WriteLn('miss i32-low') except on E: ERangeError do Hit('i32') end;
      { UInt32 }
      U32 := 99;
      A[U32] := 1;
      U32 := High(UInt32);
      try X := A[U32]; WriteLn('miss u32-high') except on E: ERangeError do Hit('u32') end;
      U32 := 100;
      try X := A[U32]; WriteLn('miss u32-len') except on E: ERangeError do Hit('u32') end;
      { Int64: a value that truncates to an in-range 32-bit index must fail }
      I64 := 99;
      A[I64] := 1;
      I64 := 4294967296;
      try X := A[I64]; WriteLn('miss i64-wrap') except on E: ERangeError do Hit('i64') end;
      I64 := High(Int64);
      try X := A[I64]; WriteLn('miss i64-high') except on E: ERangeError do Hit('i64') end;
      I64 := Low(Int64);
      try A[I64] := 1; WriteLn('miss i64-low') except on E: ERangeError do Hit('i64') end;
      { UInt64: above High(Int64) }
      U64 := 99;
      A[U64] := 1;
      U64 := High(UInt64);
      try X := A[U64]; WriteLn('miss u64-high') except on E: ERangeError do Hit('u64') end;
      U64 := 9223372036854775808;
      try X := A[U64]; WriteLn('miss u64-sign') except on E: ERangeError do Hit('u64') end;
      { enum: Length 2, so cBlue (ordinal 2) is out }
      SetLength(A, 2);
      C := cGreen;
      A[C] := 1;
      C := cBlue;
      try X := A[C]; WriteLn('miss enum') except on E: ERangeError do Hit('enum') end;
      { element kinds: float, string, interface; and the address of an element }
      SetLength(D, 2);
      D[1] := 2.5;
      try D[2] := 1.0; WriteLn('miss float-w') except on E: ERangeError do Hit('f') end;
      try WriteLn(D[2]); WriteLn('miss float-r') except on E: ERangeError do Hit('f') end;
      SetLength(S, 2);
      S[1] := 'str';
      try S[2] := 'x'; WriteLn('miss str-w') except on E: ERangeError do Hit('s') end;
      try WriteLn(S[-1]); WriteLn('miss str-r') except on E: ERangeError do Hit('s') end;
      SetLength(T, 1);
      T[0] := TThing.Create();
      try T[1] := TThing.Create(); WriteLn('miss intf-w') except on E: ERangeError do Hit('t') end;
      try X := T[1].Id(); WriteLn('miss intf-r') except on E: ERangeError do Hit('t') end;
      try P := @A[2]; WriteLn('miss addr') except on E: ERangeError do Hit('p') end;
      P := @A[1];
      P^ := 7;
      WriteLn(Hits, ' ', A[1], ' ', D[1]:0:1, ' ', S[1], ' ', T[0].Id());
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(Src, '26 7 2.5 str 42' + LE + 'done' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_ClosureCapture_RaisesERangeError;
const
  Src = '''
    program Clos;
    uses SysUtils;
    type TProc = reference to procedure;
    var P: TProc;
    procedure Make;
    var L: array of Int;
    begin
      SetLength(L, 1);
      P := procedure
        begin
          try
            L[1] := 2;
            WriteLn('miss')
          except
            on E: ERangeError do WriteLn('closure: ', E.Message)
          end;
          L[0] := 3;
          WriteLn(L[0])
        end
    end;
    begin
      Make();
      P()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(Src, 'closure: Range check error' + LE + '3' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_MoreShapes_RaiseERangeError;
const
  Src = '''
    program DynBoundsMore;
    uses SysUtils;
    type
      TProc = reference to procedure;
      TBig = set of 0..127;
      IFoo = interface function Get: Int32; end;
      TFoo = class(TObject, IFoo) function Get: Int32; end;
      TRec = record N: Int32; S: String; end;
      THolder = record
        IA: array of IFoo;
        FA: array of Float64;
        RA: array of TRec;
      end;
      TInner = class Arr: array of Int32; end;
      TOuter = class Inner: TInner; end;
    var
      G: array of Int32; RA: array of TRec; CA: array of TProc; JA: array of TBig;
      E: array of Int32; H: THolder; O: TOuter; F: IFoo; X: Int32; P: ^Int32;
    function TFoo.Get: Int32; begin Result := 1 end;
    function GetArr: array of Int32; begin Result := G end;
    function MkRec: TRec; begin Result.N := 1; Result.S := IntToStr(5) + 'x' end;
    procedure Hit(const AName: string; AP: TProc);
    begin
      try
        AP();
        WriteLn('miss ', AName)
      except
        on Ex: ERangeError do WriteLn(AName)
      end
    end;
    begin
      SetLength(G, 2); SetLength(RA, 1); SetLength(CA, 1); SetLength(JA, 1);
      SetLength(H.IA, 1); SetLength(H.FA, 1); SetLength(H.RA, 1);
      O := TOuter.Create(); O.Inner := TInner.Create(); SetLength(O.Inner.Arr, 1);
      F := TFoo.Create();
      Hit('call-read', procedure begin X := GetArr()[2] end);
      Hit('call-write', procedure begin GetArr()[2] := 1 end);
      Hit('call-inc', procedure begin Inc(GetArr()[-1]) end);
      Hit('intf-field-write', procedure begin H.IA[1] := F end);
      Hit('intf-field-read', procedure begin F := H.IA[1] end);
      Hit('float-field-write', procedure begin H.FA[1] := 1.5 end);
      Hit('rec-field-write', procedure begin H.RA[1] := MkRec() end);
      Hit('rec-elem-call-rhs', procedure begin RA[1] := MkRec() end);
      Hit('chain-write', procedure begin O.Inner.Arr[1] := 1 end);
      Hit('chain-read', procedure begin X := O.Inner.Arr[1] end);
      Hit('closure-write', procedure begin CA[1] := procedure begin end end);
      Hit('closure-call', procedure begin CA[1]() end);
      Hit('jumbo-write', procedure begin JA[1] := [100] end);
      Hit('addr-empty', procedure begin P := @E[0] end);
      GetArr()[1] := 4; H.FA[0] := 2.5; RA[0] := MkRec(); O.Inner.Arr[0] := 3;
      WriteLn(G[1], ' ', Trunc(H.FA[0] * 2), ' ', RA[0].S, ' ', O.Inner.Arr[0]);
      O.Inner.Free(); O.Free()
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src,
    'call-read' + LE + 'call-write' + LE + 'call-inc' + LE +
    'intf-field-write' + LE + 'intf-field-read' + LE + 'float-field-write' + LE +
    'rec-field-write' + LE + 'rec-elem-call-rhs' + LE + 'chain-write' + LE +
    'chain-read' + LE + 'closure-write' + LE + 'closure-call' + LE +
    'jumbo-write' + LE + 'addr-empty' + LE + '4 5 5x 3' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_BadIndexWrite_ValueNotEvaluated;
const
  Src = '''
    program DynBoundsOrder;
    uses SysUtils;
    type
      TProc = reference to procedure;
      TRec = record N: Int32; S: String; end;
      TBox = class N: Int32; end;
      THolder = record IA: array of Int32; FA: array of Float64; end;
      TOwner = class FArr: array of String; procedure Probe; end;
      TStrArr = array of String;
    var
      IA: array of Int32; SA: array of String; FA: array of Float64;
      RA: array of TRec; BA: array of TBox; CA: array of TProc;
      M: array of array of Int32; H: THolder; Ow: TOwner; Calls: Int32;
    function VI: Int32; begin Calls := Calls + 1; Result := 1 end;
    function VS: String; begin Calls := Calls + 1; Result := IntToStr(Calls) + 's' end;
    function VF: Float64; begin Calls := Calls + 1; Result := 1.5 end;
    function VR: TRec; begin Calls := Calls + 1; Result.S := IntToStr(Calls) + 'r' end;
    function VB: TBox; begin Calls := Calls + 1; Result := TBox.Create() end;
    function VC: TProc; begin Calls := Calls + 1; Result := procedure begin end end;
    function GetIA: array of Int32; begin Result := IA end;
    procedure Hit(const AName: string; AP: TProc);
    var Before: Int32;
    begin
      Before := Calls;
      try
        AP();
        WriteLn('miss ', AName)
      except
        on Ex: ERangeError do
          if Calls = Before then WriteLn(AName) else WriteLn(AName, ' evaluated the value')
      end
    end;
    procedure TOwner.Probe;
    begin
      Hit('self-string', procedure begin FArr[3] := VS() end)
    end;
    procedure ByVar(var V: TStrArr);
    var Before: Int32;
    begin
      Before := Calls;
      try
        V[3] := VS();
        WriteLn('miss var-string')
      except
        on Ex: ERangeError do
          if Calls = Before then WriteLn('var-string')
          else WriteLn('var-string evaluated the value')
      end
    end;
    begin
      SetLength(IA, 1); SetLength(SA, 1); SetLength(FA, 1); SetLength(RA, 1);
      SetLength(BA, 1); SetLength(CA, 1); SetLength(M, 1); SetLength(M[0], 1);
      SetLength(H.IA, 1); SetLength(H.FA, 1);
      Ow := TOwner.Create(); SetLength(Ow.FArr, 1);
      Hit('int', procedure begin IA[5] := VI() end);
      Hit('string', procedure begin SA[5] := VS() end);
      Hit('float', procedure begin FA[5] := VF() end);
      Hit('record', procedure begin RA[5] := VR() end);
      Hit('class', procedure begin BA[5] := VB() end);
      Hit('closure', procedure begin CA[5] := VC() end);
      Hit('outer', procedure begin M[5][0] := VI() end);
      Hit('inner', procedure begin M[0][5] := VI() end);
      Hit('call-base', procedure begin GetIA()[5] := VI() end);
      Hit('field-int', procedure begin H.IA[5] := VI() end);
      Hit('field-float', procedure begin H.FA[5] := VF() end);
      Hit('negative', procedure begin IA[-1] := VI() end);
      Ow.Probe();
      ByVar(SA);
      SA[0] := VS(); IA[0] := VI();
      WriteLn(SA[0], ' ', IA[0], ' ', Calls);
      Ow.Free()
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src,
    'int' + LE + 'string' + LE + 'float' + LE + 'record' + LE + 'class' + LE +
    'closure' + LE + 'outer' + LE + 'inner' + LE + 'call-base' + LE +
    'field-int' + LE + 'field-float' + LE + 'negative' + LE + 'self-string' + LE +
    'var-string' + LE + '1s 1 2' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_PointerOfDynArray;
const
  Src = '''
    program PtrOfDyn;
    type TRec = record A: array of Int32; end;
    var A: array of Int32; Q: Pointer; R: TRec; M: array of array of Int32;
    begin
      Q := Pointer(A);
      WriteLn(Q = nil);
      SetLength(A, 2); A[0] := 7; A[1] := 8;
      Q := Pointer(A);
      WriteLn(PInt32(Q)^);
      R.A := A;
      WriteLn(Pointer(R.A) = Pointer(A));
      SetLength(A, 0);
      WriteLn(Pointer(A) = nil);
      SetLength(M, 1); SetLength(M[0], 1); M[0][0] := 6;
      WriteLn(PInt32(Pointer(M[0]))^)
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src, 'True' + LE + '7' + LE + 'True' + LE + 'True' + LE +
    '6' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_ValueResizesTheArray;
const
  Src = '''
    program DynResize;
    uses SysUtils;
    type
      TProc = reference to procedure;
      TBig = set of 0..127;
      TRec = record N: Int32; S: String; end;
      TPair = array[0..1] of String;
      IFoo = interface function Get: Int32; end;
      TFoo = class(TObject, IFoo) N: Int32; function Get: Int32; end;
      TBox = class N: Int32; end;
      TOwner = class FA: array of Int32; procedure Run; function GrowSelf: Int32; end;
      TIntArr = array of Int32;
    var
      IA: array of Int32; SA: array of String; DA: array of Float64;
      GA: array of Float32; RA: array of TRec; PA: array of TPair;
      CA: array of TProc; JA: array of TBig; XA: array of IFoo;
      BA: array of TBox; MA: array of TIntArr; Ow: TOwner;
    const BIG = 50000;
    function TFoo.Get: Int32; begin Result := N end;
    function GI: Int32; begin SetLength(IA, BIG); Result := 5 end;
    function GS: String; begin SetLength(SA, BIG); Result := IntToStr(6) + 's' end;
    function GD: Float64; begin SetLength(DA, BIG); Result := 2.5 end;
    function GG: Float32; begin SetLength(GA, BIG); Result := 1.5 end;
    function GR: TRec; begin SetLength(RA, BIG); Result.N := 7; Result.S := IntToStr(7) + 'r' end;
    function GP: TPair; begin SetLength(PA, BIG); Result[0] := IntToStr(8) + 'p'; Result[1] := 'q' end;
    function GC: TProc; begin SetLength(CA, BIG); Result := procedure begin WriteLn('closure ran') end end;
    function GJ: TBig; begin SetLength(JA, BIG); Result := [100] end;
    function GX: IFoo; var F: TFoo; begin SetLength(XA, BIG); F := TFoo.Create(); F.N := 9; Result := F end;
    function GB: TBox; begin SetLength(BA, BIG); Result := TBox.Create(); Result.N := 10 end;
    function GM: TIntArr; begin SetLength(MA, BIG); SetLength(Result, 1); Result[0] := 11 end;
    { M[I][J] := V where V resizes M[I]: the inner array is pinned from its
      read to the store, so the write lands in it -- the array as the
      statement found it -- and is lost with it, never in freed memory.
      SetLength copied the pinned block, so the new array keeps the old
      value 3 }
    function GMI: Int32; begin SetLength(MA[0], BIG); Result := 15 end;
    function TOwner.GrowSelf: Int32; begin SetLength(FA, BIG); Result := 12 end;
    procedure TOwner.Run; begin FA[0] := GrowSelf(); WriteLn(FA[0]) end;
    procedure ByVar(var V: TIntArr);
      function GV: Int32; begin SetLength(V, BIG); Result := 13 end;
    begin
      V[0] := GV(); WriteLn(V[0])
    end;
    procedure Captured;
    var L: TIntArr;
      function GL: Int32; begin SetLength(L, BIG); Result := 14 end;
    begin
      SetLength(L, 1); L[0] := GL(); WriteLn(L[0])
    end;
    var T: TIntArr;
    begin
      SetLength(IA, 1); IA[0] := GI(); WriteLn(IA[0]);
      SetLength(SA, 1); SA[0] := GS(); WriteLn(SA[0]);
      SetLength(DA, 1); DA[0] := GD(); WriteLn(Trunc(DA[0] * 2));
      SetLength(GA, 1); GA[0] := GG(); WriteLn(Trunc(GA[0] * 2));
      SetLength(RA, 1); RA[0] := GR(); WriteLn(RA[0].N, RA[0].S);
      SetLength(PA, 1); PA[0] := GP(); WriteLn(PA[0][0], PA[0][1]);
      SetLength(CA, 1); CA[0] := GC(); CA[0]();
      SetLength(JA, 1); JA[0] := GJ(); WriteLn(100 in JA[0]);
      SetLength(XA, 1); XA[0] := GX(); WriteLn(XA[0].Get());
      SetLength(BA, 1); BA[0] := GB(); WriteLn(BA[0].N); BA[0].Free();
      SetLength(MA, 1); MA[0] := GM(); WriteLn(MA[0][0]);
      Ow := TOwner.Create(); SetLength(Ow.FA, 1); Ow.Run(); Ow.Free();
      SetLength(T, 1); ByVar(T); WriteLn(Length(T));
      Captured();
      SetLength(MA, 1); SetLength(MA[0], 1); MA[0][0] := 3;
      MA[0][0] := GMI();
      WriteLn(MA[0][0], ' ', Length(MA[0]));
      WriteLn(Length(IA), ' done')
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src,
    '5' + LE + '6s' + LE + '5' + LE + '3' + LE + '77r' + LE + '8pq' + LE +
    'closure ran' + LE + 'True' + LE + '9' + LE + '10' + LE + '11' + LE +
    '12' + LE + '13' + LE + '50000' + LE + '14' + LE + '3 50000' + LE +
    '50000 done' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_EvaluatedOnce_Shrink_GetterPins;
const
  Src = '''
    program DynOnce;
    uses SysUtils;
    type
      TIntArr = array of Int32;
      THold = class Arr: TIntArr; end;
      IGrow = interface function Grow: Int32; end;
      TGrow = class(TObject, IGrow) function Grow: Int32; end;
      TProps = class function GetG: Int32; property G: Int32 read GetG; end;
    var
      Made, Idx: Int32; Last: THold; A: TIntArr; M: array of TIntArr;
      Gi: IGrow; Pr: TProps; R: THold;
    function MakeObj: THold;
    begin
      Made := Made + 1;
      Last := THold.Create(); SetLength(Last.Arr, 2);
      Result := Last
    end;
    function Next: Int32; begin Idx := Idx + 1; Result := 1 end;
    function Shrink: Int32; begin SetLength(A, 1); Result := 9 end;
    function TGrow.Grow: Int32; begin SetLength(M[0], 50000); Result := 5 end;
    function TProps.GetG: Int32; begin SetLength(M[0], 60000); Result := 6 end;
    begin
      MakeObj().Arr[1] := 7;
      WriteLn('made ', Made, ' stored ', Last.Arr[1]);
      Last.Free();
      SetLength(A, 3);
      A[Next()] := 4;
      R := THold.Create(); SetLength(R.Arr, 3);
      R.Arr[Next()] := 5;
      WriteLn('index evaluated ', Idx, ' ', A[1], ' ', R.Arr[1]);
      R.Free();
      SetLength(A, 3);
      try
        A[2] := Shrink();
        WriteLn('miss shrink')
      except
        on E: ERangeError do WriteLn('shrink ', Length(A))
      end;
      SetLength(M, 1); SetLength(M[0], 1); M[0][0] := 3;
      Gi := TGrow.Create();
      M[0][0] := Gi.Grow();
      WriteLn('intf ', M[0][0], ' ', Length(M[0]));
      Pr := TProps.Create();
      M[0][0] := Pr.G;
      WriteLn('getter ', M[0][0], ' ', Length(M[0]));
      Pr.Free()
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src,
    'made 1 stored 7' + LE + 'index evaluated 2 4 5' + LE + 'shrink 1' + LE +
    'intf 3 50000' + LE + 'getter 3 60000' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestRun_LeftToRight_ArrayIndexValue;
const
  Src = '''
    program LeftToRight;
    uses SysUtils;
    type
      TIntArr = array of Int32;
      TSA = array[0..2] of Int32;
      THold = class Arr: TIntArr; end;
      TRec = record Arr: TIntArr; end;
    var
      G: TIntArr; M: array of TIntArr; H: THold; R: TRec; S: String;
      T: String; X: Int32; C: Int32;
    function Tr(const AWhat: string; AN: Int32): Int32;
    begin T := T + AWhat; Result := AN end;
    function F: TIntArr; begin T := T + 'F'; Result := G end;
    function GetM: array of TIntArr; begin T := T + 'M'; Result := M end;
    function MakeObj: THold; begin T := T + 'O'; Result := H end;
    function GetSA: TSA; begin T := T + 'S'; Result[1] := 4 end;
    function GetStr: String; begin T := T + 'S'; Result := S end;
    procedure Show(const AName: string); begin WriteLn(AName, ' ', T); T := '' end;
    begin
      SetLength(G, 3); SetLength(M, 3); SetLength(M[1], 3);
      H := THold.Create(); SetLength(H.Arr, 3); SetLength(R.Arr, 3);
      S := 'abc';
      F()[Tr('i', 1)] := Tr('v', 5); Show('w-call');
      M[Tr('i', 1)][Tr('j', 2)] := Tr('v', 6); Show('w-chain');
      GetM()[Tr('i', 1)][Tr('j', 2)] := Tr('v', 7); Show('w-callchain');
      MakeObj().Arr[Tr('i', 1)] := Tr('v', 8); Show('w-recv');
      R.Arr[Tr('i', 1)] := Tr('v', 9); Show('w-field');
      G[Tr('i', 0)] := Tr('v', 3); Show('w-named');
      X := F()[Tr('i', 1)]; Show('r-call');
      X := M[Tr('i', 1)][Tr('j', 2)]; Show('r-chain');
      X := GetM()[Tr('i', 1)][Tr('j', 2)]; Show('r-callchain');
      X := MakeObj().Arr[Tr('i', 1)]; Show('r-recv');
      X := GetSA()[Tr('i', 1)]; Show('r-static');
      C := Ord(GetStr()[Tr('i', 1)]); Show('r-string');
      X := F()[Tr('i', 1)] + Tr('k', 1); Show('r-sum');
      WriteLn(G[0], G[1], M[1][2], H.Arr[1], R.Arr[1], X, C);
      H.Free()
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src,
    'w-call Fiv' + LE + 'w-chain ijv' + LE + 'w-callchain Mijv' + LE +
    'w-recv Oiv' + LE + 'w-field iv' + LE + 'w-named iv' + LE +
    'r-call Fi' + LE + 'r-chain ij' + LE + 'r-callchain Mij' + LE +
    'r-recv Oi' + LE + 'r-static Si' + LE + 'r-string Si' + LE +
    'r-sum Fik' + LE + '35789698' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestDebug_ShrinkingValue_NoLeak;
begin
  AssertLeakFreeOnAll('''
    program ShrinkNoLeak;
    uses SysUtils;
    type
      TProc = reference to procedure;
      TRec = record N: Int32; S: String; end;
      IFoo = interface function Get: Int32; end;
      TFoo = class(TObject, IFoo) function Get: Int32; end;
      TBox = class N: Int32; end;
      TIntArr = array of Int32;
      THold = record SA: array of String; end;
    var
      SA: array of String; BA: array of TBox; DA: array of TIntArr;
      XA: array of IFoo; CA: array of TProc; RA: array of TRec; H: THold;
      Caught: Int32;
    function TFoo.Get: Int32; begin Result := 1 end;
    function VS: String; begin SetLength(SA, 1); Result := IntToStr(7) + 's' end;
    function VB: TBox; begin SetLength(BA, 1); Result := TBox.Create() end;
    function VD: TIntArr; begin SetLength(DA, 1); SetLength(Result, 2) end;
    function VX: IFoo; begin SetLength(XA, 1); Result := TFoo.Create() end;
    function VC: TProc; var K: Int32;
    begin SetLength(CA, 1); K := 3; Result := procedure begin K := K + 1 end end;
    function VR: TRec; begin SetLength(RA, 1); Result.S := IntToStr(8) + 'r' end;
    function VH: String; begin SetLength(H.SA, 1); Result := IntToStr(9) + 'h' end;
    procedure Probe(AP: TProc);
    begin
      try AP() except on E: ERangeError do Caught := Caught + 1 end
    end;
    begin
      SetLength(SA, 3); Probe(procedure begin SA[2] := VS() end);
      SetLength(BA, 3); Probe(procedure begin BA[2] := VB() end);
      SetLength(DA, 3); Probe(procedure begin DA[2] := VD() end);
      SetLength(XA, 3); Probe(procedure begin XA[2] := VX() end);
      SetLength(CA, 3); Probe(procedure begin CA[2] := VC() end);
      SetLength(RA, 3); Probe(procedure begin RA[2] := VR() end);
      SetLength(H.SA, 3); Probe(procedure begin H.SA[2] := VH() end);
      WriteLn('caught ', Caught);
      SA := nil; BA := nil; DA := nil; XA := nil; CA := nil; RA := nil; H.SA := nil
    end.
    ''', 'caught 7');
end;

procedure TE2EDynBoundsTests.TestDebug_IndexOrValueDropsTheBase_NoLeak;
begin
  AssertLeakFreeOnAll('''
    program DropsBase;
    uses SysUtils;
    type
      TIntArr = array of Int32;
      THold = class Arr: TIntArr; end;
      IFoo = interface function Get: Int32; end;
      TFoo = class(TObject, IFoo) N: Int32; function Get: Int32; end;
    var
      S: String; Items: array of THold; T: String; XA: array of IFoo;
      FA: array of Float64; G: TIntArr; Q: IFoo; D: Float64; F0: TFoo;
    function TFoo.Get: Int32; begin Result := N end;
    function Tr(const AWhat: string; AN: Int32): Int32;
    begin T := T + AWhat; Result := AN end;
    function Reassign: Int32; begin S := IntToStr(42) + 'xyz'; Result := 1 end;
    function GetS: String; begin Result := S end;
    function K: Int32; begin Result := 0 end;
    function Drop: Int32; begin Items[0] := nil; Result := 7 end;
    function FX: array of IFoo; begin T := T + 'X'; Result := XA end;
    function FD: array of Float64; begin T := T + 'D'; Result := FA end;
    function F: TIntArr; begin T := T + 'F'; Result := G end;
    begin
      { a named string is read where it is used, after the index ('2' of
        '42xyz'); a string from a call is evaluated first ('0' of '10abc') }
      S := IntToStr(10) + 'abc';
      WriteLn(Ord(S[Reassign()]));
      S := IntToStr(10) + 'abc';
      WriteLn(Ord(GetS()[Reassign()]));
      SetLength(Items, 1); Items[0] := THold.Create(); SetLength(Items[0].Arr, 1);
      Items[K()].Arr[0] := Drop();
      WriteLn(Items[0] = nil);
      SetLength(XA, 1); F0 := TFoo.Create(); F0.N := 3; XA[0] := F0;
      SetLength(FA, 1); FA[0] := 2.5; SetLength(G, 1);
      Q := FX()[Tr('i', 0)];
      D := FD()[Tr('i', 0)];
      Inc(F()[Tr('i', 0)]);
      WriteLn(T, ' ', Q.Get(), ' ', Trunc(D * 2), ' ', G[0]);
      Q := nil; XA := nil; Items := nil;
      WriteLn('done')
    end.
    ''', '50' + #10 + '48' + #10 + 'True' + #10 + 'XiDiFi 3 5 1' + #10 + 'done');
end;

procedure TE2EDynBoundsTests.TestDebug_RemainingShapes_LeftToRight_NoLeak;
begin
  AssertLeakFreeOnAll('''
    program Remaining;
    uses SysUtils;
    type
      TIntArr = array of Int32;
      TSA = array[0..2] of Int32;
      THold = class S: String; Arr: TIntArr; end;
      TRec = record Arr: TIntArr; SA: TSA; end;
    var
      H: TRec; DA: array of TSA; O: THold; T: String; X: Int32; Buf: TSA;
      R2: TRec; P: Pointer; KeepArr: TIntArr; KeepDA: array of TSA;
      T2: String; PNamed: PChar;
    function Tr(const AWhat: string; AN: Int32): Int32;
    begin T := T + AWhat; Result := AN end;
    function ReplaceArr: Int32;
    begin H.Arr := nil; SetLength(H.Arr, 4); H.Arr[1] := 9; Result := 1 end;
    function GrowDA: Int32; begin SetLength(DA, 50000); DA[0][1] := 8; Result := 1 end;
    function GrowDA2: Int32; begin SetLength(DA, 60000); Result := 6 end;
    function MakeObj: THold; begin T := T + 'O'; Result := O end;
    function FP: Pointer; begin T := T + 'P'; Result := P end;
    procedure Show(const AName: string); begin WriteLn(AName, ' ', T); T := '' end;
    begin
      { the old blocks stay alive under KeepArr / KeepDA, so a read through
        a stale pointer shows their old values (3, 4) }
      SetLength(H.Arr, 2); H.Arr[1] := 3; KeepArr := H.Arr;
      X := H.Arr[ReplaceArr()];
      WriteLn('field-read ', X);
      SetLength(DA, 1); DA[0][1] := 4; KeepDA := DA;
      X := DA[0][GrowDA()];
      WriteLn('static-in-dyn ', X, ' ', Length(DA));
      KeepDA := DA;
      DA[0][2] := GrowDA2();
      WriteLn('w-static-in-dyn ', DA[0][2], ' ', KeepDA[0][2]);
      O := THold.Create(); O.S := IntToStr(10) + 'abc';
      MakeObj().S[Tr('i', 1)] := Chr(Tr('v', 122));
      Show('w-strfield'); WriteLn(O.S);
      P := @Buf;
      PChar(FP())[Tr('i', 0)] := Chr(Tr('v', 7));
      Show('w-pchar'); WriteLn(Buf[0]);
      R2.SA[Tr('i', 1)] := Tr('v', 5);
      Show('w-sfield'); WriteLn(R2.SA[1]);
      Buf[Tr('i', 2)] := Tr('v', 3);
      Show('w-static-named');
      O.S[Tr('i', 2)] := Chr(Tr('v', 121));
      Show('w-strfield-named');
      T2 := IntToStr(10) + 'abc';
      T2[Tr('i', 0)] := Chr(Tr('v', 120));
      Show('w-str-named'); WriteLn(T2, ' ', O.S);
      P := @Buf;
      PNamed := P;
      { byte 1 of Buf[0] (7) becomes 9: Buf[0] = 7 + 9 * 256 = 2311 }
      PNamed[Tr('i', 1)] := Chr(Tr('v', 9));
      Show('w-pchar-named'); WriteLn(Buf[0], Buf[2]);
      MakeObj().Arr := nil;
      O.Free(); H.Arr := nil; DA := nil; KeepArr := nil; KeepDA := nil;
      WriteLn('done')
    end.
    ''', 'field-read 9' + #10 + 'static-in-dyn 8 50000' + #10 + 'w-static-in-dyn 6 0' + #10 +
      'w-strfield Oiv' + #10 + '1zabc' + #10 + 'w-pchar Piv' + #10 + '7' + #10 +
      'w-sfield iv' + #10 + '5' + #10 + 'w-static-named iv' + #10 +
      'w-strfield-named iv' + #10 + 'w-str-named iv' + #10 + 'x0abc 1zybc' + #10 +
      'w-pchar-named iv' + #10 + '23113' + #10 + 'done');
end;

procedure TE2EDynBoundsTests.TestRun_ValueChangesIndexOrPointer;
const
  Src = '''
    program ValueChanges;
    type
      TSA = array[0..3] of Int32;
      TRec = record SA: TSA; end;
    var
      G: Int32; SA: TSA; R: TRec; A: array of Int32; Buf1, Buf2: TSA;
      P: PChar; X: Int32;
    function Next: Int32; begin G := 3; Result := 7 end;
    function Swap: Int32; begin P := PChar(@Buf2); Result := 5 end;
    function SwapIdx: Int32; begin P := PChar(@Buf2); Result := 0 end;
    begin
      G := 1; SA[G] := Next(); WriteLn(SA[1], SA[3]);
      G := 1; R.SA[G] := Next(); WriteLn(R.SA[1], R.SA[3]);
      SetLength(A, 4); G := 1; A[G] := Next(); WriteLn(A[1], A[3]);
      P := PChar(@Buf1); P[0] := Chr(Swap()); WriteLn(Buf1[0], Buf2[0]);
      Buf2[0] := 66; P := PChar(@Buf1); Buf1[0] := 65;
      X := Ord(P[SwapIdx()]); WriteLn(X)
    end.
    ''';
begin
  { the index is taken before the value (element 1, not 3); a named pointer
    is read where it is used: after the value (Buf2), after the index
    (Buf2's 66) }
  AssertRunsOnAll(Src, '70' + LE + '70' + LE + '70' + LE + '05' + LE + '66' + LE, 0);
end;

procedure TE2EDynBoundsTests.TestDebug_StringElemOrder_RelocationRaise_NoLeak;
begin
  AssertLeakFreeOnAll('''
    program RelocRaise;
    uses SysUtils;
    type
      TSS = array[0..1] of String;
      TItem = record SA: array of String; end;
      TItemS = record SA: TSS; end;
    var
      Strs: array of String; T: String; DA: array of TSS; Items: array of TItem;
      Caught: Int32; DB: array of TSS; ItemsS: array of TItemS;
    function Tr(const AWhat: string; AN: Int32): Int32;
    begin T := T + AWhat; Result := AN end;
    function VS: String; begin SetLength(DA, 1); Result := IntToStr(7) + 's' end;
    function VI: String; begin SetLength(Items, 1); Result := IntToStr(8) + 'i' end;
    function K1: Int32; begin Result := 1 end;
    function VFree: Int32; begin DB := nil; Result := 120 end;
    function VIS: String; begin SetLength(ItemsS, 1); Result := IntToStr(9) + 'j' end;
    begin
      SetLength(Strs, 2); Strs[1] := IntToStr(10) + 'abc';
      Strs[Tr('K', 1)][Tr('J', 0)] := Chr(Tr('V', 120));
      WriteLn(T, ' ', Strs[1]);
      SetLength(DA, 2);
      try
        DA[1][0] := VS()
      except
        on E: ERangeError do Caught := Caught + 1
      end;
      SetLength(Items, 2); SetLength(Items[1].SA, 1);
      try
        Items[1].SA[0] := VI()
      except
        on E: ERangeError do Caught := Caught + 1
      end;
      { a string inside a static array inside a dynamic one, reached through
        a call: located last (it cannot be pinned), so a value that frees
        DB makes the locating check raise -- never a store into freed
        memory }
      SetLength(DB, 2); DB[1][1] := IntToStr(10) + 'abc';
      try
        DB[K1()][1][0] := Chr(VFree())
      except
        on E: ERangeError do Caught := Caught + 1
      end;
      { a static-array field of an element of a shrinking dynamic array: the
        receiver's check raises, the owned value is released }
      SetLength(ItemsS, 2);
      try
        ItemsS[1].SA[0] := VIS()
      except
        on E: ERangeError do Caught := Caught + 1
      end;
      WriteLn('caught ', Caught);
      Strs := nil; DA := nil; Items := nil; DB := nil; ItemsS := nil
    end.
    ''', 'KJV x0abc' + #10 + 'caught 4');
end;

procedure TE2EDynBoundsTests.TestRun_NoSysUtils_ExitCode201;
const
  Src = '''
    program DynBoundsNoSysUtils;
    var
      exa: array of array of Boolean;
      i: Int;
    begin
      SetLength(exa, 4);
      for i := 0 to 3 do
        SetLength(exa[i], 4);
      WriteLn(exa[3, 3]);
      WriteLn(exa[3, 4]);
      WriteLn('not reached')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { the harness captures stderr with stdout }
  AssertRunsOnAll(Src,
    'False' + LE + 'Runtime error: range check error' + LE, 201);
end;

initialization
  RegisterTest(TE2EDynBoundsTests);

end.
