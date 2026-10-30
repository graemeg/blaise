{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Functional.Tests;

{ Phase 8 (anonymous methods): the Functional vocabulary unit —
  TFunc/TPredicate/TAction/TComparison aliases resolve and invoke, and
  TDelegatedComparer bridges a TComparison<T> closure into IComparer<T>. }

interface

uses
  blaise.testing;

type
  TFunctionalTests = class(TTestCase)
  published
    procedure TestFunc_AliasResolvesAndInvokes;
    procedure TestPredicate_AliasResolvesAndInvokes;
    procedure TestAction_AliasResolvesAndInvokes;
    procedure TestComparison_AliasResolvesAndInvokes;
    procedure TestDelegatedComparer_RoundTrip;
    procedure TestDelegatedComparer_CapturingClosure;
  end;

implementation

uses
  Functional, Generics.Defaults;

procedure TFunctionalTests.TestFunc_AliasResolvesAndInvokes;
var
  F: TFunc<Int, string>;
begin
  F := function(AArg: Int): string
    begin
      Result := 'v' + IntToStr(AArg)
    end;
  AssertEquals('TFunc invokes', 'v41', F(41))
end;

procedure TFunctionalTests.TestPredicate_AliasResolvesAndInvokes;
var
  P: TPredicate<Int>;
begin
  P := function(AValue: Int): Boolean
    begin
      Result := AValue > 10
    end;
  AssertTrue('11 satisfies', P(11));
  AssertFalse('9 fails', P(9))
end;

procedure TFunctionalTests.TestAction_AliasResolvesAndInvokes;
var
  A: TAction<Int>;
  Sum: Int;
begin
  Sum := 0;
  A := procedure(AValue: Int)
    begin
      Sum := Sum + AValue
    end;
  A(20);
  A(22);
  AssertEquals('action accumulated via capture', 42, Sum)
end;

procedure TFunctionalTests.TestComparison_AliasResolvesAndInvokes;
var
  C: TComparison<Int>;
begin
  C := function(ALeft, ARight: Int): Int32
    begin
      Result := ALeft - ARight
    end;
  AssertTrue('less', C(1, 2) < 0);
  AssertTrue('greater', C(5, 2) > 0);
  AssertEquals('equal', 0, C(3, 3))
end;

procedure TFunctionalTests.TestDelegatedComparer_RoundTrip;
var
  Cmp: IComparer<Int>;
begin
  Cmp := TDelegatedComparer<Int>.Create(
    function(ALeft, ARight: Int): Int32
      begin
        Result := ALeft - ARight
      end);
  AssertTrue('less through interface', Cmp.Compare(1, 9) < 0);
  AssertTrue('greater through interface', Cmp.Compare(9, 1) > 0);
  AssertEquals('equal through interface', 0, Cmp.Compare(4, 4))
end;

procedure TFunctionalTests.TestDelegatedComparer_CapturingClosure;
var
  Cmp: IComparer<Int>;
  Descending: Boolean;
begin
  { The comparison closure captures a local — the comparer must keep the
    environment alive for its own lifetime. }
  Descending := True;
  Cmp := TDelegatedComparer<Int>.Create(
    function(ALeft, ARight: Int): Int32
      begin
        if Descending then
          Result := ARight - ALeft
        else
          Result := ALeft - ARight
      end);
  AssertTrue('descending order', Cmp.Compare(1, 9) > 0)
end;

initialization
  RegisterTest(TFunctionalTests);

end.
