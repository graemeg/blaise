{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Functional;

{ Functional type vocabulary (docs/anonymous-methods-design.adoc, Phase 8).

  Canonical closure-typed aliases shared by the standard library and user
  code, mirroring Delphi's System.SysUtils vocabulary:

    TFunc<T, R>     — one-argument function closure
    TPredicate<T>   — boolean test closure
    TAction<T>      — one-argument procedure closure
    TComparison<T>  — three-way ordering closure (negative / 0 / positive)

  plus the bridge into the comparer world:

    TDelegatedComparer<T> — wraps a TComparison<T> closure as an
    IComparer<T> (Generics.Defaults), so closure-based orderings plug into
    any comparer-taking API. }

interface

uses
  Generics.Defaults;

type
  { One-argument function closure: R := F(Arg). }
  TFunc<T, R> = reference to function(AArg: T): R;

  { Two-argument function closure: R := F(A, B) — accumulator shape for
    TList<T>.Reduce. }
  TFunc2<T1, T2, R> = reference to function(AArg1: T1; AArg2: T2): R;

  { Boolean test closure: True iff AValue satisfies the predicate. }
  TPredicate<T> = reference to function(AValue: T): Boolean;

  { One-argument procedure closure — a side-effecting callback. }
  TAction<T> = reference to procedure(AValue: T);

  { Three-way ordering closure: negative if ALeft < ARight, zero if equal,
    positive if ALeft > ARight. }
  TComparison<T> = reference to function(ALeft, ARight: T): Int32;

  { Adapter: present a TComparison<T> closure as an IComparer<T>.  The
    comparer holds a strong reference to the closure (and thus its captured
    environment) for its own lifetime. }
  TDelegatedComparer<T> = class(IComparer<T>)
  private
    FComparison: TComparison<T>;
  public
    constructor Create(AComparison: TComparison<T>);
    function Compare(A, B: T): Int32;
  end;

implementation

constructor TDelegatedComparer<T>.Create(AComparison: TComparison<T>);
begin
  FComparison := AComparison
end;

function TDelegatedComparer<T>.Compare(A, B: T): Int32;
begin
  Result := FComparison(A, B)
end;

end.
