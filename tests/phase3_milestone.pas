{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program Phase3Milestone;

{ Phase 3 milestone: exercises TList<Integer> and TDictionary<string,Integer>.
  Must produce correct output and zero valgrind leaks. }

type
  TIntList = class
    FData:     ^Int;
    FCount:    Int;
    FCapacity: Int;
    procedure Grow;
    procedure Add(Value: Int);
    function  Get(AIndex: Int): Int;
    procedure Delete(AIndex: Int);
    procedure Destroy;
    property Count: Int read FCount;
  end;

  TStrIntDict = class
    FKeys:     ^string;
    FValues:   ^Int;
    FCount:    Int;
    FCapacity: Int;
    procedure Grow;
    function  FindKey(Key: string): Int;
    procedure Add(Key: string; Value: Int);
    function  TryGetValue(Key: string; var Value: Int): Boolean;
    function  ContainsKey(Key: string): Boolean;
    procedure Remove(Key: string);
    procedure Destroy;
    property Count: Int read FCount;
  end;

procedure TIntList.Grow;
var
  NewCap: Int;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Int));
  Self.FCapacity := NewCap
end;

procedure TIntList.Add(Value: Int);
var
  Dest: ^Int;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(Int);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TIntList.Get(AIndex: Int): Int;
var
  Src: ^Int;
begin
  Src    := Self.FData + AIndex * SizeOf(Int);
  Result := Src^
end;

procedure TIntList.Delete(AIndex: Int);
var
  Src: ^Int;
  Dst: ^Int;
  I:   Int;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Int);
    Src  := Self.FData + (I + 1) * SizeOf(Int);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TIntList.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

procedure TStrIntDict.Grow;
var
  NewCap: Int;
  OldCap: Int;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 8
  else
    NewCap := OldCap * 2;
  Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(string));
  { Zero-init new string slots so ARC Release of "old" value is safe }
  ZeroMem(Self.FKeys + OldCap * SizeOf(string),
          (NewCap - OldCap) * SizeOf(string));
  Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Int));
  Self.FCapacity := NewCap
end;

function TStrIntDict.FindKey(Key: string): Int;
var
  I:   Int;
  Ptr: ^string;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(string);
    if Ptr^ = Key then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TStrIntDict.Add(Key: string; Value: Int);
var
  Idx:  Int;
  KPtr: ^string;
  VPtr: ^Int;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr  := Self.FValues + Idx * SizeOf(Int);
    VPtr^ := Value
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow();
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(string);
    VPtr  := Self.FValues + Self.FCount * SizeOf(Int);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1
  end
end;

function TStrIntDict.TryGetValue(Key: string; var Value: Int): Boolean;
var
  Idx:  Int;
  VPtr: ^Int;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(Int);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TStrIntDict.ContainsKey(Key: string): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TStrIntDict.Remove(Key: string);
var
  Idx:  Int;
  I:    Int;
  KDst: ^string;
  KSrc: ^string;
  VDst: ^Int;
  VSrc: ^Int;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(string);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(string);
      VDst  := Self.FValues + I * SizeOf(Int);
      VSrc  := Self.FValues + (I + 1) * SizeOf(Int);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    { Release the duplicate last string slot left behind by the shift }
    KDst := Self.FKeys + (Self.FCount - 1) * SizeOf(string);
    KDst^ := nil;
    Self.FCount := Self.FCount - 1
  end
end;

procedure TStrIntDict.Destroy;
var
  I:   Int;
  Ptr: ^string;
begin
  { Release all stored strings before freeing the backing store }
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FKeys + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

var
  List:  TIntList;
  Dict:  TStrIntDict;
  V:     Int;
  Found: Boolean;

begin
  { --- TList<Integer> --- }
  List := TIntList.Create;
  List.Add(10);
  List.Add(20);
  List.Add(30);
  List.Add(40);
  List.Add(50);

  WriteLn('list.count=', List.Count);    { 5 }
  WriteLn('list[0]=', List.Get(0));      { 10 }
  WriteLn('list[4]=', List.Get(4));      { 50 }

  List.Delete(1);
  WriteLn('count_after_delete=', List.Count);    { 4 }
  WriteLn('list[1]_after_delete=', List.Get(1)); { 30 }

  List.Free();

  { --- TDictionary<string,Integer> --- }
  Dict := TStrIntDict.Create;
  Dict.Add('alpha', 1);
  Dict.Add('beta',  2);
  Dict.Add('gamma', 3);
  Dict.Add('delta', 4);

  WriteLn('dict.count=', Dict.Count);     { 4 }

  Found := Dict.TryGetValue('beta', V);
  WriteLn('beta=', V);                    { 2 }

  Found := Dict.ContainsKey('gamma');
  WriteLn('has_gamma=', Found);           { 1 }

  Dict.Add('beta', 99);
  Found := Dict.TryGetValue('beta', V);
  WriteLn('beta_after_update=', V);       { 99 }

  Dict.Remove('alpha');
  WriteLn('count_after_remove=', Dict.Count);  { 3 }
  Found := Dict.ContainsKey('alpha');
  WriteLn('has_alpha_after_remove=', Found);   { 0 }

  Dict.Free()
end.
