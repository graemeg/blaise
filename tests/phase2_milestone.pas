{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program Phase2Milestone;

{ Phase 2 milestone: singly-linked list using TObject descendants.
  Exercises:
    - Class inheritance (TNode → TMarkedNode)
    - Virtual method dispatch (GetTag override)
    - Properties (Value, Next, Count, Head)
    - Self-referential class field (FNext: TNode)
    - try/finally for guaranteed cleanup
    - 'is' type test
  Must compile, produce correct output, and show zero valgrind leaks. }

type
  { Base list node: integer value + link to next }
  TNode = class
    FValue: Int;
    FNext:  TNode;
    function GetTag: Int; virtual;
    property Value: Int read FValue;
    property Next:  TNode   read FNext;
  end;

  { Marked node: identical to TNode but GetTag returns 1 instead of 0 }
  TMarkedNode = class(TNode)
    function GetTag: Int; override;
  end;

  { Singly-linked list, push-at-front / pop-from-front }
  TLinkedList = class
    FHead:  TNode;
    FCount: Int;
    procedure Push(Value: Int);
    procedure PushMarked(Value: Int);
    function  Pop: Int;
    procedure Walk;
    procedure Clear;
    property Count: Int read FCount;
    property Head:  TNode   read FHead;
  end;

{ ---- TNode ---- }

function TNode.GetTag: Int;
begin
  Result := 0
end;

{ ---- TMarkedNode ---- }

function TMarkedNode.GetTag: Int;
begin
  Result := 1
end;

{ ---- TLinkedList ---- }

procedure TLinkedList.Push(Value: Int);
var
  N: TNode;
begin
  N        := TNode.Create;
  N.FValue := Value;
  N.FNext  := Self.FHead;
  Self.FHead  := N;
  Self.FCount := Self.FCount + 1
end;

procedure TLinkedList.PushMarked(Value: Int);
var
  N: TMarkedNode;
begin
  N        := TMarkedNode.Create;
  N.FValue := Value;
  N.FNext  := Self.FHead;
  Self.FHead  := N;
  Self.FCount := Self.FCount + 1
end;

function TLinkedList.Pop: Int;
var
  N: TNode;
begin
  N           := Self.FHead;
  Result      := N.FValue;
  Self.FHead  := N.FNext;
  Self.FCount := Self.FCount - 1;
  N.Free()
end;

procedure TLinkedList.Walk;
var
  N:      TNode;
  Marked: Boolean;
begin
  N := Self.FHead;
  while N <> nil do
  begin
    WriteLn('  value=', N.Value);
    WriteLn('  tag=', N.GetTag());
    Marked := N is TMarkedNode;
    WriteLn('  marked=', Marked);
    N := N.Next
  end
end;

procedure TLinkedList.Clear;
var
  N:    TNode;
  Next: TNode;
begin
  N := Self.FHead;
  while N <> nil do
  begin
    Next := N.FNext;
    N.Free();
    N := Next
  end;
  Self.FHead  := nil;
  Self.FCount := 0
end;

{ ---- Main ---- }

var
  List: TLinkedList;
  V:    Int;

begin
  List := TLinkedList.Create;
  try
    { Build list: push 10, 20 (plain), 30 (marked), 40 (plain)
      After four pushes the front is 40 → 30(marked) → 20 → 10 }
    List.Push(10);
    List.Push(20);
    List.PushMarked(30);
    List.Push(40);

    WriteLn('count=', List.Count);          { 4 }
    WriteLn('--- walk ---');
    List.Walk();                             { 40/tag0, 30/tag1/marked, 20/tag0, 10/tag0 }

    { Pop two values off the front }
    V := List.Pop();
    WriteLn('pop=', V);                     { 40 }
    V := List.Pop();
    WriteLn('pop=', V);                     { 30 }

    WriteLn('count_after_pops=', List.Count);   { 2 }
  finally
    List.Clear();
    List.Free()
  end
end.
