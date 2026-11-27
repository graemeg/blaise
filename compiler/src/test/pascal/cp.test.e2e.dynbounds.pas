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
    var A: array of Int32; Q: Pointer; R: TRec;
    begin
      Q := Pointer(A);
      WriteLn(Q = nil);
      SetLength(A, 2); A[0] := 7; A[1] := 8;
      Q := Pointer(A);
      WriteLn(PInt32(Q)^);
      R.A := A;
      WriteLn(Pointer(R.A) = Pointer(A));
      SetLength(A, 0);
      WriteLn(Pointer(A) = nil)
    end.
    ''';
begin
  AssertRTLRunsOnAll(Src, 'True' + LE + '7' + LE + 'True' + LE + 'True' + LE, 0);
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
