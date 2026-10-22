{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.retiredbugs;

{ Regression guards for BUGS.md entries retired on 2026-10-22 without a
  test of their own.

  A triage of the July-September entries found these fixed on both macOS
  arm64 and x86-64 by later work, but nothing pinned their original repro,
  so a regression would have gone unnoticed.  Each test runs the entry's
  repro (named after its id) on every ISA the host can execute and asserts
  the output the bug used to get wrong. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ERetiredBugTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { BUG-20260723-incdec-string-elem: Inc/Dec on a string element compiles,
      changes only that byte, and copies on write (the shared copy keeps its
      bytes) }
    procedure TestRun_IncDecStringElement_CopyOnWrite;
    { BUG-20260722-static-intf-class-var: an interface-typed static class var
      is stored, read and called through }
    procedure TestRun_StaticInterfaceClassVar;
    { BUG-20260722-itab-arg-type-coercion: an interface call converts its
      arguments to the method's parameter types (Integer -> Single, Double ->
      Single, Integer -> Double) }
    procedure TestRun_InterfaceCall_CoercesArgs;
    { BUG-20260722-native-procvar-float-args: float arguments through an
      'of object' method pointer, a closure and a procedural field (variable
      and literal arguments, inside a method too) }
    procedure TestRun_FloatArgs_ThroughMethodPtrClosureAndProcField;
    { BUG-20260722-discarded-sret-call-no-buffer: a discarded record result
      from an implicit-Self method, a procedural field and a procedural
      variable, and a nested function with captures, in assignment and
      discarded position }
    procedure TestRun_DiscardedSretCalls_AllForms;
    { BUG-030: a nested function returning a large record, capturing a
      method's Self, local and parameter, and a plain routine's local }
    procedure TestRun_NestedSretFunction_WithCaptures;
    { BUG-20260922-arm64-member-const-array-not-emitted: class and record
      member const arrays read with constant and variable indices }
    procedure TestRun_MemberConstArrays;
    { BUG-20261004-arm64-global-intf-var-arg: a global interface variable
      passed to var and out interface parameters }
    procedure TestRun_GlobalInterfaceVar_AsVarAndOutArg;
    { BUG-20261004-arm64-record-temp-field-leak: a record call result and a
      record list element read without being stored release their managed
      fields }
    procedure TestRun_RecordTempFieldRead_NoLeak;
    { BUG-20260804-qbe-varparam-record-indexed-getter (native side): a
      record element of a TList read through a var-parameter receiver }
    procedure TestRun_VarParamReceiver_RecordListElement;
  end;

implementation

const
  LE = #10;

procedure TE2ERetiredBugTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-retiredbugs');
end;

procedure TE2ERetiredBugTests.TestRun_IncDecStringElement_CopyOnWrite;
const
  Src = '''
    program P;
    var S, T: string;
    begin
      S := 'abc';
      T := S;
      Inc(S[1]);
      Dec(S[0], 2);
      WriteLn(S, ' ', T)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '_cc abc' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_StaticInterfaceClassVar;
const
  Src = '''
    program P;
    type
      IGreet = interface function Name: string; end;
      TGreet = class(TObject, IGreet) function Name: string; end;
      TBox = class static var SI: IGreet; end;
    function TGreet.Name: string; begin Result := 'hi' end;
    var G: IGreet;
    begin
      G := TGreet.Create();
      TBox.SI := G;
      WriteLn(TBox.SI.Name())
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'hi' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_InterfaceCall_CoercesArgs;
const
  Src = '''
    program P;
    type
      ICalc = interface
        function F(a: Single; n: Integer): Integer;
        function G(d: Double; n: Integer): Integer;
      end;
      TCalc = class(TObject, ICalc)
      public
        function F(a: Single; n: Integer): Integer;
        function G(d: Double; n: Integer): Integer;
      end;
    function TCalc.F(a: Single; n: Integer): Integer;
    begin Result := Trunc(a * 10) + n end;
    function TCalc.G(d: Double; n: Integer): Integer;
    begin Result := Trunc(d * 10) + n end;
    var C: ICalc;
    begin
      C := TCalc.Create();
      WriteLn(C.F(1, 100));
      WriteLn(C.F(1.5, 100));
      WriteLn(C.G(2, 100))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '110' + LE + '115' + LE + '120' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_FloatArgs_ThroughMethodPtrClosureAndProcField;
const
  Src = '''
    program P;
    type
      TM = function(a: Double): Double of object;
      TR = reference to function(a: Double): Double;
      TOb = class
        FP: function(a: Double): Double of object;
        K: Double;
        function Twice(a: Double): Double;
        procedure Go;
      end;
    function TOb.Twice(a: Double): Double; begin Result := a * K end;
    procedure TOb.Go; begin WriteLn(Trunc(FP(3.5) * 10)) end;
    var O: TOb; M: TM; R: TR; V, W, Z: Double;
    begin
      O := TOb.Create(); O.K := 2.0;
      M := @O.Twice;
      V := 3.5; W := 99.0; Z := W;
      WriteLn(Trunc(M(V) * 10), ' ', Trunc(M(1.25) * 100));
      R := function(a: Double): Double begin Result := a * 2.0 end;
      WriteLn(Trunc(R(V) * 10), ' ', Trunc(R(0.5) * 10));
      O.FP := @O.Twice;
      WriteLn(Trunc(O.FP(4.5) * 10));
      O.Go()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '70 250' + LE + '70 10' + LE + '90' + LE + '70' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_DiscardedSretCalls_AllForms;
const
  Src = '''
    program KD;
    type
      TR = record S: string; A, B, C, D: Integer; end;
      TFn = function: TR;
      TFoo = class
        N: Integer;
        FMk: TFn;
        function MakeR: TR;
        procedure Run;
      end;
    function Mk: TR; begin Result.S := 'x' + IntToStr(7); Result.A := 1 end;
    function TFoo.MakeR: TR; begin Result.S := 'y' + IntToStr(N); Result.D := N end;
    procedure TFoo.Run; begin MakeR(); MakeR(); FMk(); WriteLn('run ', N) end;
    procedure Outer;
    var X: Integer; R: TR;
      function Nest: TR; begin Result.A := X; Result.S := 'n' end;
    begin
      X := 7; R := Nest(); WriteLn('nest ', R.A); Nest()
    end;
    var F: TFoo; PF: TFn;
    begin
      F := TFoo.Create(); F.N := 5; F.FMk := @Mk;
      F.Run();
      PF := @Mk; PF(); PF();
      Outer();
      WriteLn('done ', F.N)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'run 5' + LE + 'nest 7' + LE + 'done 5' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_NestedSretFunction_WithCaptures;
const
  Src = '''
    program B30;
    type
      TBig = record A, B, C, D, E: Integer; S: string; end;
      TObj = class
        N: Integer;
        function Run(K: Integer): Integer;
      end;
    function TObj.Run(K: Integer): Integer;
    var L: Integer; R: TBig;
      function Mk(X: Integer): TBig;
      begin Result.A := N + X + L; Result.E := K; Result.S := 's' + IntToStr(N) end;
    begin
      L := 100;
      R := Mk(1);
      WriteLn(R.A, ' ', R.E, ' ', R.S, ' ', Mk(2).A);
      Result := R.A
    end;
    procedure Outer;
    var X: Integer; R: TBig;
      function Nest: TBig; begin Result.A := X; Result.D := X * 2 end;
    begin X := 7; R := Nest(); WriteLn(R.A, ' ', R.D, ' ', Nest().D) end;
    var O: TObj;
    begin
      O := TObj.Create(); O.N := 5;
      WriteLn(O.Run(3));
      Outer()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '106 3 s5 107' + LE + '106' + LE + '7 14 14' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_MemberConstArrays;
const
  Src = '''
    program A1;
    type
      TC = class
      public
        const Names: array[0..1] of Integer = (7, 8);
      end;
      TRc = record
        const Vals: array[0..2] of Integer = (4, 5, 6);
      end;
    var I: Integer;
    begin
      I := 1;
      WriteLn(TC.Names[0], ' ', TC.Names[I], ' ', TRc.Vals[2], ' ', TRc.Vals[I])
    end.
    ''';
begin
  AssertRunsOnAll(Src, '7 8 6 5' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_GlobalInterfaceVar_AsVarAndOutArg;
const
  Src = '''
    program A2;
    type
      IG = interface function N: Integer; end;
      TG = class(TObject, IG) V: Integer; function N: Integer; end;
    function TG.N: Integer; begin Result := V end;
    procedure Swap(var X: IG; out Y: IG);
    var T: TG;
    begin
      T := TG.Create(); T.V := X.N() + 1; Y := T; X := nil
    end;
    var GA, GB: IG; T: TG;
    begin
      T := TG.Create(); T.V := 4; GA := T;
      Swap(GA, GB);
      WriteLn(GA = nil, ' ', GB.N())
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'True 5' + LE, 0);
end;

procedure TE2ERetiredBugTests.TestRun_RecordTempFieldRead_NoLeak;
const
  Src = '''
    program A3;
    uses Generics.Collections;
    type
      TR = record Name: string; O: TObject; function Get: string; end;
    function TR.Get: string; begin Result := Name end;
    function F(I: Integer): TR;
    begin Result.Name := 'n' + IntToStr(I); Result.O := TObject.Create() end;
    var L: TList<TR>; R: TR; I, N: Integer; S: string;
    begin
      L := TList<TR>.Create(); R.Name := 'x' + IntToStr(1);
      R.O := TObject.Create(); L.Add(R);
      N := 0;
      for I := 1 to 20 do
      begin
        S := F(I).Name; N := N + Length(S);
        S := F(I).Get(); N := N + Length(L[0].Name)
      end;
      WriteLn('total ', N);
      L.Free()
    end.
    ''';
begin
  AssertLeakFreeOnAll(Src, 'total 91');
end;

procedure TE2ERetiredBugTests.TestRun_VarParamReceiver_RecordListElement;
const
  Src = '''
    program A4;
    uses Generics.Collections;
    type
      TTok = record Line: Integer; S: string; end;
      THolder = record Toks: TList<TTok>; end;
    procedure Show(var AH: THolder);
    begin WriteLn(AH.Toks[0].Line, ' ', AH.Toks[0].S) end;
    var H: THolder; T: TTok;
    begin
      H.Toks := TList<TTok>.Create(); T.Line := 12; T.S := 'k'; H.Toks.Add(T);
      Show(H)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '12 k' + LE, 0);
end;

initialization
  RegisterTest(TE2ERetiredBugTests);

end.
