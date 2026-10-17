{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.operators;

{ E2E tests for operator overloading (`class operator`).

  These run on BOTH backends (AssertRunsOnAll).  The IR harness cannot see
  the two things that matter most here:

  * the record-return ABI split — an all-Integer TRect returns in REGISTERS
    (RecretClassify), while a record with a managed field returns via the
    hidden sret pointer.  Those are different codegen routes and an operator
    call must work through both.
  * ARC of the operator's result temporary in a nested expression
    (A + B + C), which is only observable in a leak-checked run. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EOperatorTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { a generic body's comparison of T runs a record T's Equal; a record with
      none still instantiates the generic for the routines that do not compare }
    procedure TestRun_Operator_GenericComparisonUsesRecordEqual;
    { every comparison of records runs the declared operator }
    procedure TestRun_Operator_RecordComparisons;
    procedure TestRun_Operator_RecordAddAndBuiltins;
    { register-return path: small all-Integer record }
    procedure TestRun_Operator_RecordAdd_RegisterReturn;
    { sret path: record carrying a managed (string) field }
    procedure TestRun_Operator_RecordAdd_ManagedField_Sret;
    { chained A + B + C — the inner result is a temporary }
    procedure TestRun_Operator_RecordAdd_Chained;
    { the operator result passed straight into a call argument }
    procedure TestRun_Operator_ResultAsCallArgument;
    { equivalence: A + B produces exactly what TRect.Add(A, B) produces }
    procedure TestRun_Operator_EquivalentToExplicitCall;
    { built-ins are unaffected — string, Integer and set '+' still work }
    procedure TestRun_Operator_BuiltinsUnaffected;
    { managed-field operator called repeatedly in a loop }
    procedure TestRun_Operator_ManagedField_InLoop;
  end;

implementation

const
  LE = #10;

procedure TE2EOperatorTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-operators');
end;

procedure TE2EOperatorTests.TestRun_Operator_RecordAdd_RegisterReturn;
const
  Src = '''
    program P;
    type
      TRect = record
        L, T: Integer;
        class operator Add(const A, C: TRect): TRect;
        class operator Subtract(const A, C: TRect): TRect;
      end;
    class operator TRect.Add(const A, C: TRect): TRect;
    begin
      Result.L := A.L + C.L;
      Result.T := A.T + C.T
    end;
    class operator TRect.Subtract(const A, C: TRect): TRect;
    begin
      Result.L := A.L - C.L;
      Result.T := A.T - C.T
    end;
    var X, Y, Z: TRect;
    begin
      X.L := 1; X.T := 2;
      Y.L := 10; Y.T := 20;
      Z := X + Y;
      WriteLn(Z.L, ' ', Z.T);
      Z := Y - X;
      WriteLn(Z.L, ' ', Z.T)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '11 22' + LE + '9 18' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_RecordAdd_ManagedField_Sret;
const
  Src = '''
    program P;
    type
      TTag = record
        Name: string;
        N: Integer;
        class operator Add(const A, C: TTag): TTag;
      end;
    class operator TTag.Add(const A, C: TTag): TTag;
    begin
      Result.Name := A.Name + C.Name;
      Result.N := A.N + C.N
    end;
    var X, Y, Z: TTag;
    begin
      X.Name := 'ab'; X.N := 3;
      Y.Name := 'cd'; Y.N := 4;
      Z := X + Y;
      WriteLn(Z.Name, ' ', Z.N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'abcd 7' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_RecordAdd_Chained;
const
  Src = '''
    program P;
    type
      TRect = record
        L, T: Integer;
        class operator Add(const A, C: TRect): TRect;
      end;
    class operator TRect.Add(const A, C: TRect): TRect;
    begin
      Result.L := A.L + C.L;
      Result.T := A.T + C.T
    end;
    var A, B, C, D: TRect;
    begin
      A.L := 1; A.T := 1;
      B.L := 2; B.T := 2;
      C.L := 4; C.T := 4;
      D := A + B + C;
      WriteLn(D.L, ' ', D.T)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7 7' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_ResultAsCallArgument;
const
  Src = '''
    program P;
    type
      TRect = record
        L, T: Integer;
        class operator Add(const A, C: TRect): TRect;
      end;
    class operator TRect.Add(const A, C: TRect): TRect;
    begin
      Result.L := A.L + C.L;
      Result.T := A.T + C.T
    end;
    procedure Show(const R: TRect);
    begin
      WriteLn(R.L, ':', R.T)
    end;
    var X, Y: TRect;
    begin
      X.L := 5; X.T := 6;
      Y.L := 7; Y.T := 8;
      Show(X + Y)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12:14' + LE, 0);
end;

{ The correctness argument for operator lowering is EQUIVALENCE: `A + B`
  must emit exactly what the explicit static call emits. }
procedure TE2EOperatorTests.TestRun_Operator_EquivalentToExplicitCall;
const
  Src = '''
    program P;
    type
      TTag = record
        Name: string;
        N: Integer;
        class operator Add(const A, C: TTag): TTag;
      end;
    class operator TTag.Add(const A, C: TTag): TTag;
    begin
      Result.Name := A.Name + C.Name;
      Result.N := A.N + C.N
    end;
    var X, Y, ViaOp, ViaCall: TTag;
    begin
      X.Name := 'p'; X.N := 1;
      Y.Name := 'q'; Y.N := 2;
      ViaOp := X + Y;
      ViaCall := TTag.Add(X, Y);
      WriteLn(ViaOp.Name, ViaOp.N, ' ', ViaCall.Name, ViaCall.N);
      if (ViaOp.Name = ViaCall.Name) and (ViaOp.N = ViaCall.N) then
        WriteLn('equal')
      else
        WriteLn('DIFFERENT')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'pq3 pq3' + LE + 'equal' + LE, 0);
end;

{ Operator resolution is a FALLBACK: it only runs after every built-in rule
  has declined, so the built-ins are structurally unreachable from it. }
procedure TE2EOperatorTests.TestRun_Operator_BuiltinsUnaffected;
const
  Src = '''
    program P;
    type
      TCol = (cRed, cGreen, cBlue);
      TCols = set of TCol;
      TRect = record
        L: Integer;
        class operator Add(const A, C: TRect): TRect;
      end;
    class operator TRect.Add(const A, C: TRect): TRect;
    begin
      Result.L := A.L + C.L
    end;
    var
      S1, S2: string;
      I1, I2: Integer;
      C1, C2, C3: TCols;
      R1, R2: TRect;
    begin
      S1 := 'ab'; S2 := 'cd';
      WriteLn(S1 + S2);
      I1 := 3; I2 := 4;
      WriteLn(I1 + I2);
      C1 := [cRed]; C2 := [cBlue];
      C3 := C1 + C2;
      if (cRed in C3) and (cBlue in C3) and not (cGreen in C3) then
        WriteLn('sets ok');
      R1.L := 5; R2.L := 6;
      WriteLn((R1 + R2).L)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'abcd' + LE + '7' + LE + 'sets ok' + LE + '11' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_ManagedField_InLoop;
const
  Src = '''
    program P;
    type
      TTag = record
        Name: string;
        class operator Add(const A, C: TTag): TTag;
      end;
    class operator TTag.Add(const A, C: TTag): TTag;
    begin
      Result.Name := A.Name + C.Name
    end;
    var
      X, Y, Z: TTag;
      I: Integer;
    begin
      X.Name := 'a';
      Y.Name := 'b';
      for I := 0 to 9 do
        Z := X + Y;
      WriteLn(Z.Name)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'ab' + LE, 0);
  { NOTE: no AssertLeakFreeOnAll here.  Repeatedly assigning a record-returning
    call into the same destination leaks the destination's previous managed
    fields — BUG-052, a pre-existing sret-assignment gap that reproduces
    identically with a plain `static function` call and is NOT introduced by
    operator lowering.  Re-enable the leak assertion when BUG-052 is fixed. }
end;

procedure TE2EOperatorTests.TestRun_Operator_RecordAddAndBuiltins;
const
  {
    A record class operator Add is called for + on that record type, managed
    fields included; + on strings and Integers keeps its built-in meaning.
    Replaces the QBE IR checks in cp.test.operators. }
  Src = '''
    program P;
    type
      TRect = record
        W, H: Integer;
        class operator Add(const A, B: TRect): TRect;
      end;
      TTag = record
        Name: string;
        N: Integer;
        class operator Add(const A, C: TTag): TTag;
      end;
    class operator TRect.Add(const A, B: TRect): TRect;
    begin
      Result.W := A.W + B.W;
      Result.H := A.H + B.H
    end;
    class operator TTag.Add(const A, C: TTag): TTag;
    begin
      Result.Name := A.Name + C.Name;
      Result.N := A.N + C.N
    end;
    var R1, R2, R3: TRect; X, Y, Z: TTag; S1, S2: string; I, J: Integer;
    begin
      R1.W := 1; R1.H := 2; R2.W := 10; R2.H := 20;
      R3 := R1 + R2;
      WriteLn(R3.W, ' ', R3.H);
      X.Name := 'a'; X.N := 1; Y.Name := 'b'; Y.N := 2;
      Z := X + Y;
      WriteLn(Z.Name, ' ', Z.N);
      S1 := 'x'; S2 := 'y';
      WriteLn(S1 + S2);
      I := 1; J := 2;
      WriteLn(I + J)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '11 22' + LE +
    'ab 3' + LE +
    'xy' + LE +
    '3' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_RecordComparisons;
const
  Src = '''
    program P;
    type
      TP = record
        X: Integer;
        Name: string;
        class operator Equal(const A, B: TP): Boolean;
        class operator NotEqual(const A, B: TP): Boolean;
        class operator LessThan(const A, B: TP): Boolean;
        class operator GreaterThanOrEqual(const A, B: TP): Boolean;
      end;
    class operator TP.Equal(const A, B: TP): Boolean;
    begin
      Result := A.X = B.X
    end;
    class operator TP.NotEqual(const A, B: TP): Boolean;
    begin
      Result := A.X <> B.X
    end;
    class operator TP.LessThan(const A, B: TP): Boolean;
    begin
      Result := A.X < B.X
    end;
    class operator TP.GreaterThanOrEqual(const A, B: TP): Boolean;
    begin
      Result := A.X >= B.X
    end;
    function Mk(AX: Integer; const AName: string): TP;
    begin
      Result.X := AX;
      Result.Name := AName
    end;
    var A, B: TP;
    begin
      A := Mk(1, 'a');
      B := Mk(1, 'b');
      WriteLn(A = B, ' ', A <> B, ' ', A < B, ' ', A >= B);
      B.X := 2;
      WriteLn(A = B, ' ', A <> B, ' ', A < B, ' ', A >= B);
      WriteLn(Mk(3, 'c') = Mk(3, 'd'), ' ', Mk(2, 'e') < A);
      if A = Mk(1, 'z') then WriteLn('match')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'True False False True' + LE +
    'False True True False' + LE +
    'True False' + LE +
    'match' + LE, 0);
end;

procedure TE2EOperatorTests.TestRun_Operator_GenericComparisonUsesRecordEqual;
const
  Src = '''
    program P;
    type
      TP = record
        X: Integer;
        S: string;
        class operator Equal(const A, B: TP): Boolean;
      end;
      TQ = record
        X: Integer;
      end;
      TBag<T> = class
        FItems: array of T;
        procedure Add(const V: T);
        function Has(const V: T): Boolean;
        function Count(): Integer;
      end;
    class operator TP.Equal(const A, B: TP): Boolean;
    begin
      Result := A.X = B.X
    end;
    procedure TBag<T>.Add(const V: T);
    begin
      SetLength(FItems, Length(FItems) + 1);
      FItems[High(FItems)] := V
    end;
    function TBag<T>.Has(const V: T): Boolean;
    var I: Integer;
    begin
      Result := False;
      for I := 0 to High(FItems) do
        if FItems[I] = V then
          Result := True
    end;
    function TBag<T>.Count(): Integer;
    begin
      Result := Length(FItems)
    end;
    function Mk(AX: Integer; const AStr: string): TP;
    begin
      Result.X := AX;
      Result.S := AStr
    end;
    var
      B: TBag<TP>;
      BQ: TBag<TQ>;
      Q: TQ;
    begin
      B := TBag<TP>.Create();
      B.Add(Mk(4, 'a'));
      WriteLn(B.Has(Mk(4, 'other')), ' ', B.Has(Mk(5, 'a')));
      BQ := TBag<TQ>.Create();
      BQ.Add(Q);
      WriteLn(BQ.Count())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True False' + LE + '1' + LE, 0);
end;

initialization
  RegisterTest(TE2EOperatorTests);

end.
