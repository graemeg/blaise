{
  Blaise stdlib - TOML writer
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - streaming TOML writer.

  TTOMLWriter emits a TOML 1.0 document by announcing structure as you go.
  Output is accumulated in a TStringBuilder.  The API follows Json.Writer:

    1. Key/value pairs - name and value in one call:
         W.WriteString('name', 'facet');
         W.WriteInt('version', 12);
         W.WriteBool('stable', True);

    2. Section headers - a key path, one element per key:
         W.BeginTable(['server', 'tls']);       // [server.tls]
         W.BeginArrayTable(['product']);         // [[product]]

    3. Inline values - array elements and inline-table members use the
       keyless '...Value' forms, exactly as in Json.Writer:
         W.WriteKey('ports');
         W.BeginArray();
           W.WriteIntValue(80);
           W.WriteIntValue(443);
         W.EndArray();                           // ports = [80, 443]
         W.WriteKey('point');
         W.BeginInlineTable();
           W.WriteInt('x', 1);
         W.EndInlineTable();                     // point = <inline table x = 1>

  Keys passed to the writer are raw names: the writer quotes them when they
  are not valid bare keys (TOMLFormatKey), so a file path is a safe key.
  Strings are always written as basic strings ("...") with TOML escapes.

  The writer does not check document-level rules such as duplicate keys or
  writing a plain key after a section header (which would place it in that
  section); Toml.Types orders its output so that it is always valid.  This
  unit does not depend on the TOML document model.
}

unit Toml.Writer;

interface

uses
  SysUtils, StrUtils;

type
  ETOMLWriterError = class(Exception)
  end;

  TTOMLContainerKind = (tckArray, tckInlineTable);

  TTOMLFrame = record
    Kind:  TTOMLContainerKind;
    Count: Int;            { elements/members emitted so far }
  end;

  TTOMLWriter = class
  private
    FSB:       TStringBuilder;
    FStack:    array of TTOMLFrame;
    FPending:  Boolean;    { a key was written; the next value fills it }
    FLineOpen: Boolean;    { a top-level key/value line awaits its newline }
    procedure PreValue;
    procedure PostValue;
    procedure WriteHeader(const AKeys: array of string; const AOpen,
      AClose: string);
  public
    constructor Create;
    destructor Destroy; override;

    { ---- section headers (top level only) ---- }
    procedure BeginTable(const AKeys: array of string);
    procedure BeginArrayTable(const AKeys: array of string);

    { ---- inline containers ---- }
    procedure BeginArray;
    procedure EndArray;
    procedure BeginInlineTable;
    procedure EndInlineTable;

    { ---- key/value pairs: name + value in one call ---- }
    procedure WriteString(const AName, AValue: string);
    procedure WriteInt(const AName: string; AValue: Int64);
    procedure WriteBool(const AName: string; AValue: Boolean);
    procedure WriteFloat(const AName: string; AValue: Float64);

    { ---- values only: array elements, or after WriteKey ---- }
    procedure WriteStringValue(const AValue: string);
    procedure WriteIntValue(AValue: Int64);
    procedure WriteBoolValue(AValue: Boolean);
    procedure WriteFloatValue(AValue: Float64);

    { ---- structure / escape hatch ---- }
    { Write a key whose value follows (a container, or WriteRaw). }
    procedure WriteKey(const AName: string);
    { Emit a verbatim, already-valid TOML value (a date-time, say). }
    procedure WriteRaw(const ATOMLFragment: string);

    { The accumulated document so far. }
    function ToString: string; override;
    { Discard all output and reset to an empty document. }
    procedure Reset;
  end;

{ Escape a string's contents for a TOML basic string (no quotes added). }
function TOMLEscape(const S: string): string;
{ S as a quoted TOML basic string. }
function TOMLQuoteString(const S: string): string;
{ True when AName can be written as a bare key (A-Z a-z 0-9 _ -). }
function TOMLIsBareKey(const AName: string): Boolean;
{ AName as written in a TOML key: bare when possible, else quoted. }
function TOMLFormatKey(const AName: string): string;
{ AValue as a TOML float: always has a '.' or exponent; inf / -inf / nan. }
function TOMLFormatFloat(AValue: Float64): string;

implementation

function TOMLEscape(const S: string): string;
var
  SB: TStringBuilder;
  B: Byte;
const
  Hex = '0123456789ABCDEF';
begin
  SB := TStringBuilder.Create();
  for B in S do
  begin
    if B = 34 then SB.Append('\"')
    else if B = 92 then SB.Append('\\')
    else if B = 8  then SB.Append('\b')
    else if B = 9  then SB.Append('\t')
    else if B = 10 then SB.Append('\n')
    else if B = 12 then SB.Append('\f')
    else if B = 13 then SB.Append('\r')
    else if (B < 32) or (B = 127) then
    begin
      SB.Append('\u00');
      SB.AppendByte(Byte(Hex[B div 16]));
      SB.AppendByte(Byte(Hex[B mod 16]));
    end
    else
      SB.AppendByte(B);
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TOMLQuoteString(const S: string): string;
begin
  Result := '"' + TOMLEscape(S) + '"';
end;

function TOMLIsBareKey(const AName: string): Boolean;
var
  B: Byte;
begin
  Result := False;
  for B in AName do
    if not (((B >= Ord('A')) and (B <= Ord('Z'))) or
            ((B >= Ord('a')) and (B <= Ord('z'))) or
            ((B >= Ord('0')) and (B <= Ord('9'))) or
            (B = Ord('_')) or (B = Ord('-'))) then
      Exit;
  Result := Length(AName) > 0;
end;

function TOMLFormatKey(const AName: string): string;
begin
  if TOMLIsBareKey(AName) then
    Result := AName
  else
    Result := TOMLQuoteString(AName);
end;

function TOMLFormatFloat(AValue: Float64): string;
var
  B: Byte;
  NeedsPoint: Boolean;
begin
  if AValue <> AValue then
  begin
    Result := 'nan';
    Exit;
  end;
  if AValue > 1.7976931348623157e308 then
  begin
    Result := 'inf';
    Exit;
  end;
  if AValue < -1.7976931348623157e308 then
  begin
    Result := '-inf';
    Exit;
  end;
  Result := DoubleToStr(AValue);
  { A float lexeme needs a fraction or an exponent, or TOML reads an integer. }
  NeedsPoint := True;
  for B in Result do
    if (B = Ord('.')) or (B = Ord('e')) or (B = Ord('E')) then
      NeedsPoint := False;
  if NeedsPoint then
    Result := Result + '.0';
end;

{ ------------------------------------------------------------------ }
{ TTOMLWriter                                                        }
{ ------------------------------------------------------------------ }

constructor TTOMLWriter.Create;
begin
  FSB := TStringBuilder.Create();
  FPending := False;
  FLineOpen := False;
end;

destructor TTOMLWriter.Destroy;
begin
  FSB.Free();
  inherited Destroy();
end;

{ Called before emitting any value.  A value after WriteKey simply fills the
  key.  Inside an array, emit the element separator and count the element.
  A keyless value at the top level is a lone value fragment (no newline, as
  TTOMLData.AsTOML uses it); a bare value inside an inline table has nowhere
  to go. }
procedure TTOMLWriter.PreValue;
var
  Top: Int;
begin
  if FPending then
  begin
    FPending := False;
    Exit;
  end;
  Top := Length(FStack) - 1;
  if Top < 0 then
    Exit;
  if FStack[Top].Kind <> tckArray then
    raise ETOMLWriterError.Create('TOML value in an inline table needs a key');
  if FStack[Top].Count > 0 then
    FSB.Append(', ');
  FStack[Top].Count := FStack[Top].Count + 1;
end;

{ Called after a value is complete: a top-level key/value line ends here. }
procedure TTOMLWriter.PostValue;
begin
  if (Length(FStack) = 0) and FLineOpen then
  begin
    FSB.AppendByte(10);
    FLineOpen := False;
  end;
end;

procedure TTOMLWriter.WriteHeader(const AKeys: array of string; const AOpen,
  AClose: string);
var
  I: Int;
begin
  if (Length(FStack) > 0) or FPending then
    raise ETOMLWriterError.Create('TOML table header inside a value');
  if Length(AKeys) = 0 then
    raise ETOMLWriterError.Create('TOML table header needs a key');
  if FSB.Length > 0 then
    FSB.AppendByte(10);   { blank line between sections }
  FSB.Append(AOpen);
  I := 0;
  while I < Length(AKeys) do
  begin
    if I > 0 then
      FSB.Append('.');
    FSB.Append(TOMLFormatKey(AKeys[I]));
    I := I + 1;
  end;
  FSB.Append(AClose);
  FSB.AppendByte(10);
end;

procedure TTOMLWriter.BeginTable(const AKeys: array of string);
begin
  WriteHeader(AKeys, '[', ']');
end;

procedure TTOMLWriter.BeginArrayTable(const AKeys: array of string);
begin
  WriteHeader(AKeys, '[[', ']]');
end;

procedure TTOMLWriter.BeginArray;
begin
  PreValue();
  FSB.Append('[');
  SetLength(FStack, Length(FStack) + 1);
  FStack[Length(FStack) - 1].Kind := tckArray;
  FStack[Length(FStack) - 1].Count := 0;
end;

procedure TTOMLWriter.EndArray;
begin
  if (Length(FStack) = 0) or (FStack[Length(FStack) - 1].Kind <> tckArray) then
    raise ETOMLWriterError.Create('EndArray without BeginArray');
  SetLength(FStack, Length(FStack) - 1);
  FSB.Append(']');
  PostValue();
end;

procedure TTOMLWriter.BeginInlineTable;
begin
  PreValue();
  FSB.Append('{');
  SetLength(FStack, Length(FStack) + 1);
  FStack[Length(FStack) - 1].Kind := tckInlineTable;
  FStack[Length(FStack) - 1].Count := 0;
end;

procedure TTOMLWriter.EndInlineTable;
var
  Cnt: Int;
begin
  if (Length(FStack) = 0) or
     (FStack[Length(FStack) - 1].Kind <> tckInlineTable) then
    raise ETOMLWriterError.Create('EndInlineTable without BeginInlineTable');
  Cnt := FStack[Length(FStack) - 1].Count;
  SetLength(FStack, Length(FStack) - 1);
  if Cnt > 0 then
    FSB.Append(' }')
  else
    FSB.Append('}');
  PostValue();
end;

procedure TTOMLWriter.WriteKey(const AName: string);
var
  Top: Int;
begin
  if FPending then
    raise ETOMLWriterError.Create('TOML key written where a value is due');
  Top := Length(FStack) - 1;
  if Top >= 0 then
  begin
    if FStack[Top].Kind <> tckInlineTable then
      raise ETOMLWriterError.Create('TOML key inside an array');
    if FStack[Top].Count > 0 then
      FSB.Append(', ')
    else
      FSB.Append(' ');
    FStack[Top].Count := FStack[Top].Count + 1;
  end
  else
    FLineOpen := True;
  FSB.Append(TOMLFormatKey(AName));
  FSB.Append(' = ');
  FPending := True;
end;

procedure TTOMLWriter.WriteStringValue(const AValue: string);
begin
  PreValue();
  FSB.Append(TOMLQuoteString(AValue));
  PostValue();
end;

procedure TTOMLWriter.WriteIntValue(AValue: Int64);
begin
  PreValue();
  FSB.Append(IntToStr(AValue));
  PostValue();
end;

procedure TTOMLWriter.WriteBoolValue(AValue: Boolean);
begin
  PreValue();
  if AValue then
    FSB.Append('true')
  else
    FSB.Append('false');
  PostValue();
end;

procedure TTOMLWriter.WriteFloatValue(AValue: Float64);
begin
  PreValue();
  FSB.Append(TOMLFormatFloat(AValue));
  PostValue();
end;

procedure TTOMLWriter.WriteRaw(const ATOMLFragment: string);
begin
  PreValue();
  FSB.Append(ATOMLFragment);
  PostValue();
end;

procedure TTOMLWriter.WriteString(const AName, AValue: string);
begin
  WriteKey(AName);
  WriteStringValue(AValue);
end;

procedure TTOMLWriter.WriteInt(const AName: string; AValue: Int64);
begin
  WriteKey(AName);
  WriteIntValue(AValue);
end;

procedure TTOMLWriter.WriteBool(const AName: string; AValue: Boolean);
begin
  WriteKey(AName);
  WriteBoolValue(AValue);
end;

procedure TTOMLWriter.WriteFloat(const AName: string; AValue: Float64);
begin
  WriteKey(AName);
  WriteFloatValue(AValue);
end;

function TTOMLWriter.ToString: string;
begin
  Result := FSB.ToString();
end;

procedure TTOMLWriter.Reset;
begin
  FSB.Free();
  FSB := TStringBuilder.Create();
  FPending := False;
  FLineOpen := False;
  SetLength(FStack, 0);
end;

end.
