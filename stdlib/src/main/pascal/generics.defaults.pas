{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Generics.Defaults;

// Blaise RTL — generic comparison and equality interfaces.
// Mirrors FPC's Generics.Defaults and Delphi's System.Generics.Defaults for
// source-level compatibility.
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.

interface

type
  { Equality comparison: Equals returns True iff A = B;
    GetHashCode returns a hash suitable for use in hash tables. }
  IEqualityComparer<T> = interface
    function Equals(A, B: T): Boolean;
    function GetHashCode(Value: T): Int32;
  end;

  { Ordering comparison: Compare returns negative if A < B,
    zero if A = B, positive if A > B. }
  IComparer<T> = interface
    function Compare(A, B: T): Int32;
  end;

  { Concrete equality comparer for Integer }
  TIntegerEqualityComparer = class(IEqualityComparer<Int32>)
    function Equals(A, B: Int32): Boolean;
    function GetHashCode(Value: Int32): Int32;
  end;

  { Concrete ordering comparer for Integer }
  TIntegerComparer = class(IComparer<Int32>)
    function Compare(A, B: Int32): Int32;
  end;

implementation

function TIntegerEqualityComparer.Equals(A, B: Int32): Boolean;
begin
  Result := A = B
end;

function TIntegerEqualityComparer.GetHashCode(Value: Int32): Int32;
begin
  Result := Value
end;

function TIntegerComparer.Compare(A, B: Int32): Int32;
begin
  if A < B then
    Result := -1
  else if A > B then
    Result := 1
  else
    Result := 0
end;

end.
