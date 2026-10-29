{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Contnrs;

// Blaise RTL — Contnrs unit.
//
// Provides TObjectList, matching the FPC contnrs unit layout so that
// compiler source using "uses Contnrs" and TObjectList works unchanged.

interface

uses
  runtime.arc;  { for _ClassRelease }

type
  { ------------------------------------------------------------------ }
  { TObjectListEnumerator                                                }
  { ------------------------------------------------------------------ }

  TObjectListEnumerator = class
    FList:  TObjectList;
    FIndex: Int;
    constructor Create(AList: TObjectList);
    function MoveNext: Boolean;
    function GetCurrent: Pointer;
    property Current: Pointer read GetCurrent;
  end;

  { ------------------------------------------------------------------ }
  { TObjectList                                                          }
  { ------------------------------------------------------------------ }

  TObjectList = class
    FData:        ^Pointer;
    FCount:       Int;
    FCapacity:    Int;
    FOwnsObjects: Boolean;
    procedure Grow;
    constructor Create(AOwnsObjects: Boolean);
    destructor Destroy; override;
    function    Add(AObject: Pointer): Int;
    function    Get(AIndex: Int): Pointer;
    procedure   Put(AIndex: Int; AObject: Pointer);
    function    IndexOf(AObject: Pointer): Int;
    procedure   Delete(AIndex: Int);
    function    Remove(AObject: Pointer): Int;
    function    Extract(AObject: Pointer): Pointer;
    procedure   Clear;
    function    GetEnumerator: TObjectListEnumerator;
    property Count: Int read FCount;
    property Items[Index: Int]: Pointer read Get write Put; default;
  end;

implementation

{ ================================================================== }
{ TObjectList                                                          }
{ ================================================================== }

procedure TObjectList.Grow;
var
  NewCap: Int;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
  Self.FCapacity := NewCap
end;

constructor TObjectList.Create(AOwnsObjects: Boolean);
begin
  Self.FOwnsObjects := AOwnsObjects
end;

destructor TObjectList.Destroy;
var
  I:   Int;
  Src: ^Pointer;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Src := Self.FData + I * SizeOf(Pointer);
    _ClassRelease(Src^);
    I := I + 1
  end;
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TObjectList.Add(AObject: Pointer): Int;
var
  Dest: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  _ClassAddRef(AObject);
  Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
  Dest^       := AObject;
  Self.FCount := Self.FCount + 1;
  Result      := Self.FCount - 1
end;

function TObjectList.Get(AIndex: Int): Pointer;
var
  Src: ^Pointer;
begin
  Src    := Self.FData + AIndex * SizeOf(Pointer);
  Result := Src^
end;

procedure TObjectList.Put(AIndex: Int; AObject: Pointer);
var
  Dest: ^Pointer;
  Old:  Pointer;
begin
  Dest  := Self.FData + AIndex * SizeOf(Pointer);
  Old   := Dest^;
  _ClassAddRef(AObject);
  Dest^ := AObject;
  _ClassRelease(Old)
end;

function TObjectList.IndexOf(AObject: Pointer): Int;
var
  I:   Int;
  Src: ^Pointer;
begin
  I      := 0;
  Result := -1;
  while I < Self.FCount do
  begin
    Src := Self.FData + I * SizeOf(Pointer);
    if Src^ = AObject then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TObjectList.Delete(AIndex: Int);
var
  I:   Int;
  Dst: ^Pointer;
  Src: ^Pointer;
begin
  Src := Self.FData + AIndex * SizeOf(Pointer);
  _ClassRelease(Src^);
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

{ Find AObject and delete it, returning the index it was found at (or -1 if it
  was not present).  Delete releases the list's reference, so when the list owns
  its objects the removed object is freed; matches TFPObjectList.Remove. }
function TObjectList.Remove(AObject: Pointer): Int;
begin
  Result := Self.IndexOf(AObject);
  if Result >= 0 then
    Self.Delete(Result)
end;

procedure TObjectList.Clear;
var
  I:   Int;
  Src: ^Pointer;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Src := Self.FData + I * SizeOf(Pointer);
    _ClassRelease(Src^);
    I := I + 1
  end;
  Self.FCount := 0
end;

function TObjectList.Extract(AObject: Pointer): Pointer;
var
  I:   Int;
  Src: ^Pointer;
  Dst: ^Pointer;
  Idx: Int;
begin
  Idx := Self.IndexOf(AObject);
  if Idx < 0 then
  begin
    Result := nil;
    Exit
  end;
  Result := AObject;
  I := Idx;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

function TObjectList.GetEnumerator: TObjectListEnumerator;
begin
  Result := TObjectListEnumerator.Create(Self)
end;

{ ================================================================== }
{ TObjectListEnumerator                                                }
{ ================================================================== }

constructor TObjectListEnumerator.Create(AList: TObjectList);
begin
  Self.FList  := AList;
  Self.FIndex := -1
end;

function TObjectListEnumerator.MoveNext: Boolean;
begin
  Self.FIndex := Self.FIndex + 1;
  Result := Self.FIndex < Self.FList.Count
end;

function TObjectListEnumerator.GetCurrent: Pointer;
begin
  Result := Self.FList.Get(Self.FIndex)
end;

end.
