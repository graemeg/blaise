{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the Contnrs unit (TObjectList).  Self-registers via the
  initialization section.

  Focus: TObjectList.Remove(AObject) — the FPC TFPObjectList.Remove parity
  method (issue #166).  Remove finds the object, deletes it at that index
  (releasing it when the list owns objects), and returns the index it was
  found at, or -1 if it was not present. }

unit Contnrs.Tests;

interface

uses
  blaise.testing, Contnrs;

type
  { A trivial element type so we can put real class instances in the list. }
  TItem = class
    Value: Int;
    constructor Create(AValue: Int);
  end;

  TContnrsTests = class(TTestCase)
  published
    procedure TestRemove_PresentObject_ReturnsIndexAndRemoves;
    procedure TestRemove_AbsentObject_ReturnsMinusOne;
    procedure TestRemove_MiddleElement_ShiftsRemainder;
    procedure TestRemove_Unowned_DoesNotFreeButUnlists;
  end;

implementation

constructor TItem.Create(AValue: Int);
begin
  Self.Value := AValue
end;

{ Remove an object that is present: returns its index, drops Count by one, and
  the object is no longer found in the list. }
procedure TContnrsTests.TestRemove_PresentObject_ReturnsIndexAndRemoves;
var
  L: TObjectList;
  A, B, C: TItem;
  Idx: Int;
begin
  L := TObjectList.Create(True);   { owns objects }
  A := TItem.Create(1);
  B := TItem.Create(2);
  C := TItem.Create(3);
  L.Add(A);
  L.Add(B);
  L.Add(C);

  Idx := L.Remove(B);
  AssertEquals('Remove returns the index the object was found at', 1, Idx);
  AssertEquals('Count drops by one after Remove', 2, L.Count);
  AssertEquals('the removed object is no longer in the list', -1, L.IndexOf(B));
  L.Destroy()
end;

{ Removing an object that is not in the list returns -1 and leaves Count alone. }
procedure TContnrsTests.TestRemove_AbsentObject_ReturnsMinusOne;
var
  L: TObjectList;
  A, Stranger: TItem;
  Idx: Int;
begin
  L := TObjectList.Create(True);
  A := TItem.Create(1);
  Stranger := TItem.Create(99);
  L.Add(A);

  Idx := L.Remove(Stranger);
  AssertEquals('Remove of an absent object returns -1', -1, Idx);
  AssertEquals('Count unchanged when the object is absent', 1, L.Count);

  Stranger.Free();     { the list never owned Stranger }
  L.Destroy()
end;

{ Removing a middle element shifts the remaining elements down so order is kept. }
procedure TContnrsTests.TestRemove_MiddleElement_ShiftsRemainder;
var
  L: TObjectList;
  A, B, C: TItem;
begin
  L := TObjectList.Create(True);
  A := TItem.Create(10);
  B := TItem.Create(20);
  C := TItem.Create(30);
  L.Add(A);
  L.Add(B);
  L.Add(C);

  L.Remove(B);
  AssertEquals('element 0 unchanged after middle Remove', 0, L.IndexOf(A));
  AssertEquals('element after the removed one shifts down', 1, L.IndexOf(C));
  AssertEquals('two elements remain', 2, L.Count);
  L.Destroy()
end;

{ An unowned list's Remove unlists the object but must not free it — the caller
  still owns it and can use it afterwards. }
procedure TContnrsTests.TestRemove_Unowned_DoesNotFreeButUnlists;
var
  L: TObjectList;
  A: TItem;
  Idx: Int;
begin
  L := TObjectList.Create(False);   { does NOT own objects }
  A := TItem.Create(42);
  L.Add(A);

  Idx := L.Remove(A);
  AssertEquals('Remove returns index 0', 0, Idx);
  AssertEquals('list is now empty', 0, L.Count);
  { A must still be alive and usable — the list did not own it. }
  AssertEquals('object survives Remove on an unowned list', 42, A.Value);

  A.Free();
  L.Destroy()
end;

initialization
  RegisterTest(TContnrsTests);
end.
