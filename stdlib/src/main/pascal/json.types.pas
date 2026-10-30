{
  Blaise stdlib - JSON document model (DOM)
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - the in-memory JSON document model.

  TJSONData is the abstract base; the concrete node types are TJSONNull,
  TJSONBoolean, TJSONString, TJSONNumber, TJSONArray and TJSONObject.  Both the
  reader (Json.Parser / Json.Reader) and any code that builds a document by hand
  target this one tree, so JSON round-trips through it.

  Building a document (the .NET-friendly tree API):

      Root := TJSONObject.Create();
      Root.Add('name', 'blaise');           // string field
      Root.Add('version', Int64(12));       // integer field
      Root.Add('stable', True);             // boolean field
      Arr := TJSONArray.Create();
      Arr.Add('DEBUG'); Arr.Add('UNIX');    // array elements
      Root.Add('defines', Arr);             // nested array (Root adopts Arr)
      WriteLn(Root.FormatJSON());           // pretty
      WriteLn(Root.AsJSON());               // compact

  Memory model: parent-owns-child.  Containers hold STRONG references to their
  children, so under Blaise ARC, releasing the root recursively releases the
  whole tree.  Every Add() overload that takes a TJSONData *adopts* the node:
  never Add the same node to two parents, and never Add a node you also keep a
  separate owning reference to and free yourself.  Use Extract() to move a node
  out of one parent before placing it in another.

  Scalars are typed nodes (jtNull/jtBoolean/jtNumber/jtString) so a parser can
  faithfully distinguish 42 from "42" from true.  Insertion order is preserved
  (parallel name/value arrays in objects) so emitted output is stable and
  diffable.

  Serialisation is delegated to Json.Writer (the single emit kernel): AsJSON is
  compact, FormatJSON is pretty.  The writer itself has no dependency on this
  unit, so streaming-only callers need not pull in the DOM.
}

unit Json.Types;

interface

uses
  SysUtils, Json.Writer;

type
  TJSONType = (jtNull, jtBoolean, jtNumber, jtString, jtArray, jtObject);

  TJSONData = class
  protected
    function GetJSONType: TJSONType; virtual; abstract;
    function GetCount: Int; virtual;             { 0 for scalars }
    function GetAsString: string; virtual;
    function GetAsInt64: Int64; virtual;
    function GetAsFloat: Float64; virtual;
    function GetAsBoolean: Boolean; virtual;
    { Drive AWriter to emit this node and its descendants. }
    procedure WriteTo(AWriter: TJSONWriter); virtual; abstract;
  public
    function IsNull: Boolean;
    function AsJSON: string;                          { compact, no whitespace }
    function FormatJSON: string; overload;            { pretty, 2-space indent }
    function FormatJSON(AIndent: Int): string; overload;

    property JSONType: TJSONType read GetJSONType;
    property Count: Int read GetCount;
    property AsString: string read GetAsString;
    property AsInt64: Int64 read GetAsInt64;
    property AsFloat: Float64 read GetAsFloat;
    property AsBoolean: Boolean read GetAsBoolean;
  end;

  TJSONNull = class(TJSONData)
  protected
    function GetJSONType: TJSONType; override;
    function GetAsString: string; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  end;

  TJSONBoolean = class(TJSONData)
  protected
    FValue: Boolean;
    function GetJSONType: TJSONType; override;
    function GetAsString: string; override;
    function GetAsBoolean: Boolean; override;
    function GetAsInt64: Int64; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  public
    constructor Create(AValue: Boolean);
    property Value: Boolean read FValue write FValue;
  end;

  TJSONString = class(TJSONData)
  protected
    FValue: string;
    function GetJSONType: TJSONType; override;
    function GetAsString: string; override;
    function GetAsInt64: Int64; override;
    function GetAsFloat: Float64; override;
    function GetAsBoolean: Boolean; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  public
    constructor Create(const AValue: string);
    property Value: string read FValue write FValue;
  end;

  { One number node with an int/float discriminator.  FText keeps the original
    lexeme so parsed numbers round-trip exactly; programmatically-built numbers
    synthesise it. }
  TJSONNumber = class(TJSONData)
  protected
    FInt:   Int64;
    FFloat: Float64;
    FIsInt: Boolean;
    FText:  string;
    function GetJSONType: TJSONType; override;
    function GetAsString: string; override;
    function GetAsInt64: Int64; override;
    function GetAsFloat: Float64; override;
    function GetAsBoolean: Boolean; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  public
    constructor CreateInt(AValue: Int64);
    constructor CreateFloat(AValue: Float64);
    { Construct from a raw, already-validated JSON number lexeme (reader path). }
    constructor CreateText(const AText: string; AIsInt: Boolean);
    property IsInteger: Boolean read FIsInt;
  end;

  TJSONArray = class(TJSONData)
  private
    FItems: array of TJSONData;   { parent owns these (strong) }
  protected
    function GetJSONType: TJSONType; override;
    function GetCount: Int; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  public
    function Add(AValue: TJSONData): Int; overload;        { TAKES OWNERSHIP }
    function Add(const AValue: string): Int; overload;     { wraps TJSONString }
    function Add(AValue: Int64): Int; overload;
    function Add(AValue: Boolean): Int; overload;
    function Add(AValue: Float64): Int; overload;
    function AddNull: Int;
    { Detach the element at AIndex and return it; the caller then owns it. }
    function Extract(AIndex: Int): TJSONData;
    { Detach and discard the element at AIndex (ARC frees it). }
    procedure Delete(AIndex: Int);
    procedure Clear;
    function GetItem(AIndex: Int): TJSONData;
    property Items[AIndex: Int]: TJSONData read GetItem; default;
  end;

  TJSONObject = class(TJSONData)
  private
    FNames:  array of string;     { parallel arrays preserve insertion order }
    FValues: array of TJSONData;  { parent owns these (strong) }
    function IndexOfName(const AName: string): Int;
    procedure RemoveIndex(AIndex: Int);
  protected
    function GetJSONType: TJSONType; override;
    function GetCount: Int; override;
    procedure WriteTo(AWriter: TJSONWriter); override;
  public
    function Add(const AName: string; AValue: TJSONData): Int; overload;  { OWNS }
    function Add(const AName: string; const AValue: string): Int; overload;
    function Add(const AName: string; AValue: Int64): Int; overload;
    function Add(const AName: string; AValue: Boolean): Int; overload;
    function Add(const AName: string; AValue: Float64): Int; overload;
    function AddNull(const AName: string): Int;
    function Find(const AName: string): TJSONData;     { nil if absent }
    function Contains(const AName: string): Boolean;
    { Detach a member and return it (nil if absent).  Use to move a node. }
    function Extract(const AName: string): TJSONData;
    { Detach and discard a member (ARC frees it).  True if it existed. }
    function Remove(const AName: string): Boolean;
    procedure Delete(AIndex: Int);
    procedure Clear;
    function GetByName(const AName: string): TJSONData;
    function GetName(AIndex: Int): string;
    function GetItem(AIndex: Int): TJSONData;
    property Values[AName: string]: TJSONData read GetByName; default;
    property Names[AIndex: Int]: string read GetName;
    property ItemsByIndex[AIndex: Int]: TJSONData read GetItem;
  end;

{ Serialise a tree.  Equivalent to AData.AsJSON / AData.FormatJSON, offered as
  free functions for callers that prefer them. }
function AsJSON(AData: TJSONData): string;
function FormatJSON(AData: TJSONData): string; overload;
function FormatJSON(AData: TJSONData; AIndent: Int): string; overload;

implementation

{ ------------------------------------------------------------------ }
{ helpers                                                             }
{ ------------------------------------------------------------------ }

{ Parse a JSON number lexeme into a Double.  The lexeme is assumed already
  validated (shape -?int(.frac)?([eE][+-]?digits)?); robust enough for
  config-sized inputs. }
function StrToFloatJSON(const S: string): Float64;
var
  I, Len, ExpSign, ExpVal, K: Int;
  Sign, Acc, Scale: Float64;
begin
  Len := Length(S);
  I := 0;
  Sign := 1.0;
  if (I < Len) and (Byte(S[I]) = Ord('-')) then begin Sign := -1.0; I := I + 1; end
  else if (I < Len) and (Byte(S[I]) = Ord('+')) then I := I + 1;

  Acc := 0.0;
  while (I < Len) and (Byte(S[I]) >= Ord('0')) and (Byte(S[I]) <= Ord('9')) do
  begin
    Acc := Acc * 10.0 + (Byte(S[I]) - Ord('0'));
    I := I + 1;
  end;

  if (I < Len) and (Byte(S[I]) = Ord('.')) then
  begin
    I := I + 1;
    Scale := 1.0;
    while (I < Len) and (Byte(S[I]) >= Ord('0')) and (Byte(S[I]) <= Ord('9')) do
    begin
      Acc := Acc * 10.0 + (Byte(S[I]) - Ord('0'));
      Scale := Scale * 10.0;
      I := I + 1;
    end;
    Acc := Acc / Scale;
  end;

  if (I < Len) and ((Byte(S[I]) = Ord('e')) or (Byte(S[I]) = Ord('E'))) then
  begin
    I := I + 1;
    ExpSign := 1;
    if (I < Len) and (Byte(S[I]) = Ord('-')) then begin ExpSign := -1; I := I + 1; end
    else if (I < Len) and (Byte(S[I]) = Ord('+')) then I := I + 1;
    ExpVal := 0;
    while (I < Len) and (Byte(S[I]) >= Ord('0')) and (Byte(S[I]) <= Ord('9')) do
    begin
      ExpVal := ExpVal * 10 + (Byte(S[I]) - Ord('0'));
      I := I + 1;
    end;
    Scale := 1.0;
    K := 0;
    while K < ExpVal do begin Scale := Scale * 10.0; K := K + 1; end;
    if ExpSign < 0 then Acc := Acc / Scale else Acc := Acc * Scale;
  end;

  Result := Sign * Acc;
end;

{ ------------------------------------------------------------------ }
{ TJSONData                                                          }
{ ------------------------------------------------------------------ }

function TJSONData.GetCount: Int;
begin
  Result := 0;
end;

function TJSONData.GetAsString: string;
begin
  Result := '';
end;

function TJSONData.GetAsInt64: Int64;
begin
  Result := 0;
end;

function TJSONData.GetAsFloat: Float64;
begin
  Result := 0.0;
end;

function TJSONData.GetAsBoolean: Boolean;
begin
  Result := False;
end;

function TJSONData.IsNull: Boolean;
begin
  Result := GetJSONType() = jtNull;
end;

function TJSONData.AsJSON: string;
var
  W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.Pretty := False;
  WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

function TJSONData.FormatJSON: string;
begin
  Result := FormatJSON(2);
end;

function TJSONData.FormatJSON(AIndent: Int): string;
var
  W: TJSONWriter;
begin
  W := TJSONWriter.Create();
  W.Pretty := True;
  W.Indent := AIndent;
  WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

{ ------------------------------------------------------------------ }
{ TJSONNull                                                          }
{ ------------------------------------------------------------------ }

function TJSONNull.GetJSONType: TJSONType;
begin
  Result := jtNull;
end;

function TJSONNull.GetAsString: string;
begin
  Result := 'null';
end;

procedure TJSONNull.WriteTo(AWriter: TJSONWriter);
begin
  AWriter.WriteNullValue();
end;

{ ------------------------------------------------------------------ }
{ TJSONBoolean                                                       }
{ ------------------------------------------------------------------ }

constructor TJSONBoolean.Create(AValue: Boolean);
begin
  FValue := AValue;
end;

function TJSONBoolean.GetJSONType: TJSONType;
begin
  Result := jtBoolean;
end;

function TJSONBoolean.GetAsString: string;
begin
  if FValue then Result := 'true' else Result := 'false';
end;

function TJSONBoolean.GetAsBoolean: Boolean;
begin
  Result := FValue;
end;

function TJSONBoolean.GetAsInt64: Int64;
begin
  if FValue then Result := 1 else Result := 0;
end;

procedure TJSONBoolean.WriteTo(AWriter: TJSONWriter);
begin
  AWriter.WriteBoolValue(FValue);
end;

{ ------------------------------------------------------------------ }
{ TJSONString                                                        }
{ ------------------------------------------------------------------ }

constructor TJSONString.Create(const AValue: string);
begin
  FValue := AValue;
end;

function TJSONString.GetJSONType: TJSONType;
begin
  Result := jtString;
end;

function TJSONString.GetAsString: string;
begin
  Result := FValue;
end;

function TJSONString.GetAsInt64: Int64;
begin
  Result := StrToInt64(FValue);
end;

function TJSONString.GetAsFloat: Float64;
begin
  Result := StrToFloatJSON(FValue);
end;

function TJSONString.GetAsBoolean: Boolean;
begin
  Result := FValue = 'true';
end;

procedure TJSONString.WriteTo(AWriter: TJSONWriter);
begin
  AWriter.WriteStringValue(FValue);
end;

{ ------------------------------------------------------------------ }
{ TJSONNumber                                                        }
{ ------------------------------------------------------------------ }

constructor TJSONNumber.CreateInt(AValue: Int64);
begin
  FInt := AValue;
  FFloat := AValue;
  FIsInt := True;
  FText := IntToStr(AValue);
end;

constructor TJSONNumber.CreateFloat(AValue: Float64);
begin
  FFloat := AValue;
  FInt := Trunc(AValue);
  FIsInt := False;
  FText := Format('%g', [AValue]);
end;

constructor TJSONNumber.CreateText(const AText: string; AIsInt: Boolean);
begin
  FText := AText;
  FIsInt := AIsInt;
  if AIsInt then
  begin
    FInt := StrToInt64(AText);
    FFloat := FInt;
  end
  else
  begin
    FFloat := StrToFloatJSON(AText);
    FInt := Trunc(FFloat);
  end;
end;

function TJSONNumber.GetJSONType: TJSONType;
begin
  Result := jtNumber;
end;

function TJSONNumber.GetAsString: string;
begin
  Result := FText;
end;

function TJSONNumber.GetAsInt64: Int64;
begin
  Result := FInt;
end;

function TJSONNumber.GetAsFloat: Float64;
begin
  Result := FFloat;
end;

function TJSONNumber.GetAsBoolean: Boolean;
begin
  Result := FFloat <> 0.0;
end;

procedure TJSONNumber.WriteTo(AWriter: TJSONWriter);
begin
  { Emit the original lexeme verbatim to preserve exact representation. }
  AWriter.WriteRaw(FText);
end;

{ ------------------------------------------------------------------ }
{ TJSONArray                                                         }
{ ------------------------------------------------------------------ }

function TJSONArray.GetJSONType: TJSONType;
begin
  Result := jtArray;
end;

function TJSONArray.GetCount: Int;
begin
  Result := Length(FItems);
end;

function TJSONArray.GetItem(AIndex: Int): TJSONData;
begin
  Result := FItems[AIndex];
end;

function TJSONArray.Add(AValue: TJSONData): Int;
begin
  SetLength(FItems, Length(FItems) + 1);
  FItems[Length(FItems) - 1] := AValue;
  Result := Length(FItems) - 1;
end;

function TJSONArray.Add(const AValue: string): Int;
begin
  Result := Add(TJSONString.Create(AValue));
end;

function TJSONArray.Add(AValue: Int64): Int;
begin
  Result := Add(TJSONNumber.CreateInt(AValue));
end;

function TJSONArray.Add(AValue: Boolean): Int;
begin
  Result := Add(TJSONBoolean.Create(AValue));
end;

function TJSONArray.Add(AValue: Float64): Int;
begin
  Result := Add(TJSONNumber.CreateFloat(AValue));
end;

function TJSONArray.AddNull: Int;
begin
  Result := Add(TJSONNull.Create());
end;

function TJSONArray.Extract(AIndex: Int): TJSONData;
var
  I: Int;
begin
  Result := FItems[AIndex];   { hold a ref so it survives the shrink }
  I := AIndex;
  while I < Length(FItems) - 1 do
  begin
    FItems[I] := FItems[I + 1];
    I := I + 1;
  end;
  SetLength(FItems, Length(FItems) - 1);
end;

procedure TJSONArray.Delete(AIndex: Int);
var
  Gone: TJSONData;
begin
  Gone := Extract(AIndex);   { dropping the local ref lets ARC free it }
end;

procedure TJSONArray.Clear;
begin
  SetLength(FItems, 0);
end;

procedure TJSONArray.WriteTo(AWriter: TJSONWriter);
var
  I: Int;
begin
  AWriter.BeginArray();
  I := 0;
  while I < Length(FItems) do
  begin
    FItems[I].WriteTo(AWriter);
    I := I + 1;
  end;
  AWriter.EndArray();
end;

{ ------------------------------------------------------------------ }
{ TJSONObject                                                        }
{ ------------------------------------------------------------------ }

function TJSONObject.GetJSONType: TJSONType;
begin
  Result := jtObject;
end;

function TJSONObject.GetCount: Int;
begin
  Result := Length(FValues);
end;

function TJSONObject.IndexOfName(const AName: string): Int;
var
  I: Int;
begin
  Result := -1;
  I := 0;
  while I < Length(FNames) do
  begin
    if FNames[I] = AName then
    begin
      Result := I;
      Exit;
    end;
    I := I + 1;
  end;
end;

procedure TJSONObject.RemoveIndex(AIndex: Int);
var
  I: Int;
begin
  I := AIndex;
  while I < Length(FNames) - 1 do
  begin
    FNames[I] := FNames[I + 1];
    FValues[I] := FValues[I + 1];
    I := I + 1;
  end;
  SetLength(FNames, Length(FNames) - 1);
  SetLength(FValues, Length(FValues) - 1);
end;

function TJSONObject.Add(const AName: string; AValue: TJSONData): Int;
begin
  SetLength(FNames, Length(FNames) + 1);
  SetLength(FValues, Length(FValues) + 1);
  FNames[Length(FNames) - 1] := AName;
  FValues[Length(FValues) - 1] := AValue;
  Result := Length(FValues) - 1;
end;

function TJSONObject.Add(const AName: string; const AValue: string): Int;
begin
  Result := Add(AName, TJSONString.Create(AValue));
end;

function TJSONObject.Add(const AName: string; AValue: Int64): Int;
begin
  Result := Add(AName, TJSONNumber.CreateInt(AValue));
end;

function TJSONObject.Add(const AName: string; AValue: Boolean): Int;
begin
  Result := Add(AName, TJSONBoolean.Create(AValue));
end;

function TJSONObject.Add(const AName: string; AValue: Float64): Int;
begin
  Result := Add(AName, TJSONNumber.CreateFloat(AValue));
end;

function TJSONObject.AddNull(const AName: string): Int;
begin
  Result := Add(AName, TJSONNull.Create());
end;

function TJSONObject.Find(const AName: string): TJSONData;
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  if Idx < 0 then Result := nil else Result := FValues[Idx];
end;

function TJSONObject.Contains(const AName: string): Boolean;
begin
  Result := IndexOfName(AName) >= 0;
end;

function TJSONObject.Extract(const AName: string): TJSONData;
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  if Idx < 0 then
    Result := nil
  else
  begin
    Result := FValues[Idx];   { hold a ref so it survives RemoveIndex }
    RemoveIndex(Idx);
  end;
end;

function TJSONObject.Remove(const AName: string): Boolean;
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  Result := Idx >= 0;
  if Result then
    RemoveIndex(Idx);
end;

procedure TJSONObject.Delete(AIndex: Int);
begin
  RemoveIndex(AIndex);
end;

procedure TJSONObject.Clear;
begin
  SetLength(FNames, 0);
  SetLength(FValues, 0);
end;

function TJSONObject.GetByName(const AName: string): TJSONData;
begin
  Result := Find(AName);
end;

function TJSONObject.GetName(AIndex: Int): string;
begin
  Result := FNames[AIndex];
end;

function TJSONObject.GetItem(AIndex: Int): TJSONData;
begin
  Result := FValues[AIndex];
end;

procedure TJSONObject.WriteTo(AWriter: TJSONWriter);
var
  I: Int;
begin
  AWriter.BeginObject();
  I := 0;
  while I < Length(FValues) do
  begin
    AWriter.WriteKey(FNames[I]);
    FValues[I].WriteTo(AWriter);
    I := I + 1;
  end;
  AWriter.EndObject();
end;

{ ------------------------------------------------------------------ }
{ free functions                                                     }
{ ------------------------------------------------------------------ }

function AsJSON(AData: TJSONData): string;
begin
  Result := AData.AsJSON();
end;

function FormatJSON(AData: TJSONData): string;
begin
  Result := AData.FormatJSON();
end;

function FormatJSON(AData: TJSONData; AIndent: Int): string;
begin
  Result := AData.FormatJSON(AIndent);
end;

end.
