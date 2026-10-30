{
  Blaise stdlib - JSON writer
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - streaming JSON writer.

  TJSONWriter emits a JSON document by announcing structure as you go: open a
  container, write fields or elements, close it.  Output is accumulated in a
  TStringBuilder, so building even a large document is O(n), not the O(n^2) of
  repeated string concatenation.

  The API has three tiers, mirroring how JSON is actually written:

    1. Object fields (the common case) - name and value in one call:
         W.WriteString('name', 'blaise');
         W.WriteInt('version', 12);
         W.WriteBool('stable', True);

    2. Array elements - value only, no name (the '...Value' forms):
         W.BeginArray();
           W.WriteStringValue('a');
           W.WriteIntValue(1);
         W.EndArray();

    3. Structure / escape hatch - when an object member's value is itself a
       nested object or array, write the key, then open the container:
         W.WriteKey('tags');
         W.BeginArray; ... W.EndArray;

  The '...Value' suffix marks the keyless (array-element) form, following the
  naming used by .NET's Utf8JsonWriter, so it is always clear at the call site
  whether a write is keyed or not.

  Separators, newlines and indentation are tracked internally; the caller never
  writes a comma or a brace by hand.  Set Pretty (and Indent) before writing for
  human-readable output; the default is compact.

  This unit is self-contained: it does not depend on a JSON document/DOM type.
  A reader and an in-memory document model are a separate, future layer.
}

unit Json.Writer;

interface

uses
  SysUtils, StrUtils;

type
  EJSONWriterError = class(Exception)
  end;

  TJSONContainerKind = (ckObject, ckArray);

  TJSONFrame = record
    Kind:  TJSONContainerKind;
    Count: Int;            { members/elements emitted so far }
  end;

  TJSONWriter = class
  private
    FSB:      TStringBuilder;
    FPretty:  Boolean;
    FIndent:  Int;            { spaces per level when pretty }
    FStack:   array of TJSONFrame;
    FPending: Boolean;            { a key was written; the next value fills it }
    procedure NewlineIndent(ALevel: Int);
    procedure PreValue;           { emit element separator / newline as needed }
    procedure WriteEscaped(const S: string);
  public
    constructor Create;
    destructor Destroy; override;

    { ---- containers ---- }
    procedure BeginObject;
    procedure EndObject;
    procedure BeginArray;
    procedure EndArray;

    { ---- object fields: name + value in one call (the common case) ---- }
    procedure WriteString(const AName, AValue: string); overload;
    procedure WriteInt(const AName: string; AValue: Int64); overload;
    procedure WriteBool(const AName: string; AValue: Boolean); overload;
    procedure WriteFloat(const AName: string; AValue: Float64); overload;
    procedure WriteNull(const AName: string);

    { ---- array elements: value only, no name ---- }
    procedure WriteStringValue(const AValue: string);
    procedure WriteIntValue(AValue: Int64);
    procedure WriteBoolValue(AValue: Boolean);
    procedure WriteFloatValue(AValue: Float64);
    procedure WriteNullValue;

    { ---- structure / escape hatch ---- }
    { Write an object member key whose value follows.  Use this when the value
      is itself a nested object or array (BeginObject / BeginArray next). }
    procedure WriteKey(const AName: string);
    { Emit a verbatim, already-formatted JSON fragment as the next value. }
    procedure WriteRaw(const AJSONFragment: string);

    { The accumulated document so far. }
    function ToString: string; override;
    { Discard all output and reset to an empty document. }
    procedure Reset;

    property Pretty: Boolean read FPretty write FPretty;
    property Indent: Int read FIndent write FIndent;
  end;

{ Escape a string's contents per RFC 8259 (no surrounding quotes added). }
function JSONEscape(const S: string): string;

implementation

function JSONEscape(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Int;
  B: Byte;
const
  Hex = '0123456789abcdef';
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if B = 34 then SB.Append('\"')          { " }
    else if B = 92 then SB.Append('\\')     { \ }
    else if B = 8  then SB.Append('\b')
    else if B = 9  then SB.Append('\t')
    else if B = 10 then SB.Append('\n')
    else if B = 12 then SB.Append('\f')
    else if B = 13 then SB.Append('\r')
    else if B < 32 then
    begin
      { other control characters -> \u00XX (Hex is 0-based in Blaise) }
      SB.Append('\u00');
      SB.AppendByte(Byte(Hex[B div 16]));
      SB.AppendByte(Byte(Hex[B mod 16]));
    end
    else
      SB.AppendByte(B);
    I := I + 1;
  end;
  Result := SB.ToString();
  SB.Free();
end;

constructor TJSONWriter.Create;
begin
  FSB := TStringBuilder.Create();
  FPretty := False;
  FIndent := 2;
  FPending := False;
end;

destructor TJSONWriter.Destroy;
begin
  FSB.Free();
  inherited Destroy();
end;

procedure TJSONWriter.NewlineIndent(ALevel: Int);
var
  I: Int;
begin
  if not FPretty then
    Exit;
  FSB.AppendByte(10);   { LF }
  I := 0;
  while I < ALevel * FIndent do
  begin
    FSB.AppendByte(32); { space }
    I := I + 1;
  end;
end;

{ Called before emitting any value.  If a key was just written the value simply
  fills it (the separator is already in place).  Otherwise, inside an array, emit
  the inter-element comma plus newline/indent and count the element.  At the top
  level nothing is needed. }
procedure TJSONWriter.PreValue;
var
  Top: Int;
begin
  if FPending then
  begin
    FPending := False;
    Exit;
  end;
  Top := Length(FStack) - 1;
  if Top >= 0 then
  begin
    if FStack[Top].Count > 0 then
      FSB.Append(',');
    NewlineIndent(Top + 1);
    FStack[Top].Count := FStack[Top].Count + 1;
  end;
end;

procedure TJSONWriter.WriteEscaped(const S: string);
begin
  FSB.Append('"');
  FSB.Append(JSONEscape(S));
  FSB.Append('"');
end;

procedure TJSONWriter.BeginObject;
begin
  PreValue();
  FSB.Append('{');
  SetLength(FStack, Length(FStack) + 1);
  FStack[Length(FStack) - 1].Kind := ckObject;
  FStack[Length(FStack) - 1].Count := 0;
end;

procedure TJSONWriter.EndObject;
var
  Cnt: Int;
begin
  Cnt := FStack[Length(FStack) - 1].Count;
  SetLength(FStack, Length(FStack) - 1);
  if Cnt > 0 then
    NewlineIndent(Length(FStack));
  FSB.Append('}');
end;

procedure TJSONWriter.BeginArray;
begin
  PreValue();
  FSB.Append('[');
  SetLength(FStack, Length(FStack) + 1);
  FStack[Length(FStack) - 1].Kind := ckArray;
  FStack[Length(FStack) - 1].Count := 0;
end;

procedure TJSONWriter.EndArray;
var
  Cnt: Int;
begin
  Cnt := FStack[Length(FStack) - 1].Count;
  SetLength(FStack, Length(FStack) - 1);
  if Cnt > 0 then
    NewlineIndent(Length(FStack));
  FSB.Append(']');
end;

procedure TJSONWriter.WriteKey(const AName: string);
var
  Top: Int;
begin
  Top := Length(FStack) - 1;
  if (Top < 0) or (FStack[Top].Kind <> ckObject) then
    raise EJSONWriterError.Create('WriteKey outside an object');
  if FStack[Top].Count > 0 then
    FSB.Append(',');
  NewlineIndent(Top + 1);
  FStack[Top].Count := FStack[Top].Count + 1;
  WriteEscaped(AName);
  if FPretty then
    FSB.Append(': ')
  else
    FSB.Append(':');
  FPending := True;
end;

{ ---- array-element (keyless) writes ---- }

procedure TJSONWriter.WriteStringValue(const AValue: string);
begin
  PreValue();
  WriteEscaped(AValue);
end;

procedure TJSONWriter.WriteIntValue(AValue: Int64);
begin
  PreValue();
  FSB.Append(IntToStr(AValue));
end;

procedure TJSONWriter.WriteBoolValue(AValue: Boolean);
begin
  PreValue();
  if AValue then
    FSB.Append('true')
  else
    FSB.Append('false');
end;

{ NOTE: float formatting uses '%g', which is a reasonable general default but
  can use exponent form and does not guarantee shortest round-trip output.
  JSON has no integer/float distinction, so prefer WriteInt for whole numbers. }
procedure TJSONWriter.WriteFloatValue(AValue: Float64);
begin
  PreValue();
  FSB.Append(Format('%g', [AValue]));
end;

procedure TJSONWriter.WriteNullValue;
begin
  PreValue();
  FSB.Append('null');
end;

procedure TJSONWriter.WriteRaw(const AJSONFragment: string);
begin
  PreValue();
  FSB.Append(AJSONFragment);
end;

{ ---- object-field (key + value) writes ---- }

procedure TJSONWriter.WriteString(const AName, AValue: string);
begin
  WriteKey(AName);
  WriteStringValue(AValue);
end;

procedure TJSONWriter.WriteInt(const AName: string; AValue: Int64);
begin
  WriteKey(AName);
  WriteIntValue(AValue);
end;

procedure TJSONWriter.WriteBool(const AName: string; AValue: Boolean);
begin
  WriteKey(AName);
  WriteBoolValue(AValue);
end;

procedure TJSONWriter.WriteFloat(const AName: string; AValue: Float64);
begin
  WriteKey(AName);
  WriteFloatValue(AValue);
end;

procedure TJSONWriter.WriteNull(const AName: string);
begin
  WriteKey(AName);
  WriteNullValue();
end;

function TJSONWriter.ToString: string;
begin
  Result := FSB.ToString();
end;

procedure TJSONWriter.Reset;
begin
  FSB.Free();
  FSB := TStringBuilder.Create();
  FPending := False;
  SetLength(FStack, 0);
end;

end.
