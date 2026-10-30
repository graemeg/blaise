{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — C size/alignment calculator (x86_64 / AArch64 SysV, LP64).

  Computes the byte size and alignment of a C type, resolving typedef
  chains and record layouts through the TCModel.  Needed to emit
  unions with their exact size: a union used by value (XEvent!) with a
  wrong size corrupts the caller's stack.  Returns False for anything
  it cannot prove — the emitter then degrades gracefully rather than
  guessing. }

unit Bindgen.Layout;

interface

uses
  SysUtils, StrUtils,
  Bindgen.Model, Bindgen.TypeMap;

{ Size and alignment of a clang qualType.  False = not computable
  (undeclared name, incomplete record, unsupported construct). }
function CTypeSizeAlign(AModel: TCModel; const AQualType: string;
  var ASize, AAlign: Int): Boolean;

{ Layout of a harvested record: struct = C field packing with padding;
  union = max member size.  False if any field is not computable. }
function RecordSizeAlign(AModel: TCModel; ARec: TCRecord;
  var ASize, AAlign: Int): Boolean;

implementation

function BuiltinSize(const ABlaiseName: string; var ASize: Int): Boolean;
begin
  Result := True;
  if ABlaiseName = 'Byte' then ASize := 1
  else if ABlaiseName = 'Boolean' then ASize := 1
  else if ABlaiseName = 'Int8' then ASize := 1
  else if ABlaiseName = 'UInt8' then ASize := 1
  else if ABlaiseName = 'Int16' then ASize := 2
  else if ABlaiseName = 'UInt16' then ASize := 2
  else if ABlaiseName = 'Int32' then ASize := 4
  else if ABlaiseName = 'UInt32' then ASize := 4
  else if ABlaiseName = 'Float32' then ASize := 4
  else if ABlaiseName = 'Int64' then ASize := 8
  else if ABlaiseName = 'UInt64' then ASize := 8
  else if ABlaiseName = 'Float64' then ASize := 8
  else if ABlaiseName = 'Pointer' then ASize := 8
  else if ABlaiseName = 'PChar' then ASize := 8
  else Result := False;
end;

function AlignUp(AValue, AAlign: Int): Int;
begin
  Result := ((AValue + AAlign - 1) div AAlign) * AAlign;
end;

function FindTypedef(AModel: TCModel; const AName: string): TCTypedef;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to AModel.Typedefs.Count - 1 do
    if AModel.Typedefs[I].Name = AName then
    begin
      Result := AModel.Typedefs[I];
      Exit;
    end;
end;

function RecordSizeAlign(AModel: TCModel; ARec: TCRecord;
  var ASize, AAlign: Int): Boolean;
var
  I: Int;
  FSize, FAlign: Int;
  Offset: Int;
begin
  Result := False;
  if not ARec.IsComplete then Exit;
  ASize := 0;
  AAlign := 1;
  if ARec.Fields.Count = 0 then
  begin
    Result := True;
    Exit;
  end;
  Offset := 0;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    if not CTypeSizeAlign(AModel, ARec.Fields[I].CType, FSize, FAlign) then
      Exit;
    if FAlign > AAlign then
      AAlign := FAlign;
    if ARec.IsUnion then
    begin
      if FSize > ASize then
        ASize := FSize;
    end
    else
    begin
      Offset := AlignUp(Offset, FAlign);
      Offset := Offset + FSize;
    end;
  end;
  if not ARec.IsUnion then
    ASize := Offset;
  ASize := AlignUp(ASize, AAlign);
  Result := True;
end;

function CTypeSizeAlign(AModel: TCModel; const AQualType: string;
  var ASize, AAlign: Int): Boolean;
var
  S: string;
  Base: string;
  CountStr: string;
  Count: Int;
  BracketPos: Int;
  Mapped: string;
  R: TCRecord;
  T: TCTypedef;
begin
  Result := False;
  S := StripQualifiers(AQualType);

  { Any pointer (including function pointers) is 8/8. }
  if EndsStr('*', S) or (Pos('(*)', S) >= 0) then
  begin
    ASize := 8;
    AAlign := 8;
    Result := True;
    Exit;
  end;

  { Fixed-size array: element size × count, element alignment. }
  BracketPos := Pos('[', S);
  if (BracketPos >= 0) and EndsStr(']', S) then
  begin
    Base := Trim(LeftStr(S, BracketPos));
    CountStr := Trim(MidStr(S, BracketPos + 1, Length(S) - BracketPos - 2));
    Count := StrToIntDef(CountStr, -1);
    if Count < 0 then Exit;
    if not CTypeSizeAlign(AModel, Base, ASize, AAlign) then Exit;
    ASize := ASize * Count;
    Result := True;
    Exit;
  end;

  { C builtins and the standard typedef vocabulary: scalar align = size. }
  Mapped := MapBuiltin(S);
  if Mapped <> '' then
  begin
    if BuiltinSize(Mapped, ASize) then
    begin
      AAlign := ASize;
      Result := True;
    end;
    Exit;
  end;

  { Named record (struct/union tag or typedef-named). }
  R := AModel.FindRecord(S);
  if R <> nil then
  begin
    Result := RecordSizeAlign(AModel, R, ASize, AAlign);
    Exit;
  end;

  { Typedef chain. }
  T := FindTypedef(AModel, S);
  if T <> nil then
    Result := CTypeSizeAlign(AModel, T.CType, ASize, AAlign);
end;

end.
