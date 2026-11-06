{
  Blaise stdlib - TOML document model
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - the in-memory TOML document model.

  TTOMLData is the abstract base; the concrete node types are TTOMLString,
  TTOMLInteger, TTOMLFloat, TTOMLBoolean, TTOMLDateTime, TTOMLArray and
  TTOMLTable.  A document is a TTOMLTable (the root table).  The reader
  (Toml.Parser / Toml.Reader) and code that builds a document by hand target
  this one tree, so TOML round-trips through it.

  Building a document:

      Root := TTOMLTable.Create();
      Root.Put('title', 'Facet');                    // string
      Root.Put('maxMemory', Int64(4096));            // integer
      Root.Put('automaticJava', True);               // boolean
      Root.EnsureTable('window').Put('width', Int64(854));   // [window]
      WriteLn(Root.AsTOML());

  Reading values without trusting the file - the typed accessors return the
  caller's default (or False for TryGet...) when a key is absent OR holds a
  value of another kind, so 'automaticJava = "yes"' does not pass for a
  Boolean:

      UseAuto := Root.GetBoolean('automaticJava', True);
      if Root.TryGetInt64('maxMemory', Mem) then ...
      Win := Root.FindTable('window');               // nil if not a table

  TOMLType tells a value's kind exactly; IsString / IsInteger / ... are the
  shorthand tests.  The As... properties are lenient conversions in the
  manner of Json.Types (AsString of a date-time is its text).

  Memory model: parent-owns-child, as in Json.Types.  Containers hold STRONG
  references to their children; releasing the root releases the whole tree.
  Add and Put adopt the node passed in: never place one node in two parents.
  Use Extract to move a node from one parent to another.

  Insertion order is preserved.  AsTOML on a table writes a document: plain
  key/value pairs first, then each sub-table as a [section] and each array of
  tables as [[sections]].  A table whose IsInline is set (the parser sets it
  for inline tables in the source) is written inline instead.  Parsed integers, floats and
  date-times keep their source text, so 0xFF stays 0xFF.  Comments and
  original layout are not kept.
}

unit Toml.Types;

interface

uses
  SysUtils, Toml.Writer;

type
  TTOMLType = (ttString, ttInteger, ttFloat, ttBoolean, ttOffsetDateTime,
    ttLocalDateTime, ttLocalDate, ttLocalTime, ttArray, ttTable);

  { Raised on misuse of the document model (a duplicate Add, say). }
  ETOMLError = class(Exception)
  end;

  { A table header's key path, one element per (unquoted) key. }
  TTOMLKeyPath = array of string;

  TTOMLData = class
  protected
    function GetTOMLType: TTOMLType; virtual; abstract;
    function GetCount: Int; virtual;             { 0 for scalars }
    function GetAsString: string; virtual;
    function GetAsInt64: Int64; virtual;
    function GetAsFloat: Float64; virtual;
    function GetAsBoolean: Boolean; virtual;
  public
    { Drive AWriter to emit this node as an inline value. }
    procedure WriteValue(AWriter: TTOMLWriter); virtual; abstract;
    function IsString: Boolean;
    function IsInteger: Boolean;
    function IsFloat: Boolean;
    function IsBoolean: Boolean;
    { Any of the four date/time kinds. }
    function IsDateTime: Boolean;
    function IsArray: Boolean;
    function IsTable: Boolean;
    { A scalar or array: its value text.  A table: a whole document. }
    function AsTOML: string; virtual;

    property TOMLType: TTOMLType read GetTOMLType;
    property Count: Int read GetCount;
    property AsString: string read GetAsString;
    property AsInt64: Int64 read GetAsInt64;
    property AsFloat: Float64 read GetAsFloat;
    property AsBoolean: Boolean read GetAsBoolean;
  end;

  TTOMLString = class(TTOMLData)
  protected
    FValue: string;
    function GetTOMLType: TTOMLType; override;
    function GetAsString: string; override;
  public
    constructor Create(const AValue: string);
    procedure WriteValue(AWriter: TTOMLWriter); override;
    property Value: string read FValue write FValue;
  end;

  { An integer.  FText keeps the source lexeme (0xFF, 1_000) so parsed values
    write back as they were read; setting Value resynthesises it. }
  TTOMLInteger = class(TTOMLData)
  protected
    FValue: Int64;
    FText:  string;
    function GetTOMLType: TTOMLType; override;
    function GetAsString: string; override;
    function GetAsInt64: Int64; override;
    function GetAsFloat: Float64; override;
    function GetAsBoolean: Boolean; override;
    procedure SetValue(AValue: Int64);
  public
    constructor Create(AValue: Int64);
    { From an already-validated TOML integer lexeme and its value. }
    constructor CreateText(const AText: string; AValue: Int64);
    procedure WriteValue(AWriter: TTOMLWriter); override;
    property Value: Int64 read FValue write SetValue;
    property Text: string read FText;
  end;

  TTOMLFloat = class(TTOMLData)
  protected
    FValue: Float64;
    FText:  string;
    function GetTOMLType: TTOMLType; override;
    function GetAsString: string; override;
    function GetAsInt64: Int64; override;
    function GetAsFloat: Float64; override;
    function GetAsBoolean: Boolean; override;
    procedure SetValue(AValue: Float64);
  public
    constructor Create(AValue: Float64);
    constructor CreateText(const AText: string; AValue: Float64);
    procedure WriteValue(AWriter: TTOMLWriter); override;
    property Value: Float64 read FValue write SetValue;
    property Text: string read FText;
  end;

  TTOMLBoolean = class(TTOMLData)
  protected
    FValue: Boolean;
    function GetTOMLType: TTOMLType; override;
    function GetAsString: string; override;
    function GetAsInt64: Int64; override;
    function GetAsBoolean: Boolean; override;
  public
    constructor Create(AValue: Boolean);
    procedure WriteValue(AWriter: TTOMLWriter); override;
    property Value: Boolean read FValue write FValue;
  end;

  { An offset date-time, local date-time, local date or local time, kept as
    its (validated) RFC 3339 text, e.g. '1979-05-27T07:32:00Z'. }
  TTOMLDateTime = class(TTOMLData)
  protected
    FKind: TTOMLType;
    FText: string;
    function GetTOMLType: TTOMLType; override;
    function GetAsString: string; override;
  public
    { AKind is ttOffsetDateTime, ttLocalDateTime, ttLocalDate or ttLocalTime.
      AText is not validated here; Toml.Parser validates what it reads. }
    constructor Create(AKind: TTOMLType; const AText: string);
    procedure WriteValue(AWriter: TTOMLWriter); override;
    property Text: string read FText;
  end;

  TTOMLArray = class(TTOMLData)
  private
    FItems: array of TTOMLData;   { parent owns these (strong) }
  protected
    function GetTOMLType: TTOMLType; override;
    function GetCount: Int; override;
  public
    procedure WriteValue(AWriter: TTOMLWriter); override;
    function Add(AValue: TTOMLData): Int; overload;        { TAKES OWNERSHIP }
    function Add(const AValue: string): Int; overload;
    function Add(AValue: Int64): Int; overload;
    function Add(AValue: Boolean): Int; overload;
    function Add(AValue: Float64): Int; overload;
    { Detach the element at AIndex and return it; the caller then owns it. }
    function Extract(AIndex: Int): TTOMLData;
    procedure Delete(AIndex: Int);
    procedure Clear;
    { True when non-empty and every element is a non-inline table: such an
      array is written as [[name]] sections. }
    function IsArrayOfTables: Boolean;
    function GetItem(AIndex: Int): TTOMLData;
    property Items[AIndex: Int]: TTOMLData read GetItem; default;
  end;

  TTOMLTable = class(TTOMLData)
  private
    FNames:  array of string;     { parallel arrays preserve insertion order }
    FValues: array of TTOMLData;  { parent owns these (strong) }
    FInline: Boolean;
    function IndexOfName(const AName: string): Int;
    procedure RemoveIndex(AIndex: Int);
    function HasPlainEntries: Boolean;
    procedure WriteBody(AWriter: TTOMLWriter; const APath: TTOMLKeyPath);
  protected
    function GetTOMLType: TTOMLType; override;
    function GetCount: Int; override;
  public
    { Write this table as an inline table. }
    procedure WriteValue(AWriter: TTOMLWriter); override;
    { Write this table as a document (sections for sub-tables). }
    procedure WriteDocument(AWriter: TTOMLWriter);
    function AsTOML: string; override;

    { Append a member.  Raises ETOMLError if AName exists.  TAKES OWNERSHIP. }
    function Add(const AName: string; AValue: TTOMLData): Int;
    { Set a member: replace an existing value in place, else append.
      TAKES OWNERSHIP of a TTOMLData. }
    procedure Put(const AName: string; AValue: TTOMLData); overload;
    procedure Put(const AName: string; const AValue: string); overload;
    procedure Put(const AName: string; AValue: Int64); overload;
    procedure Put(const AName: string; AValue: Boolean); overload;
    procedure Put(const AName: string; AValue: Float64); overload;
    function Find(const AName: string): TTOMLData;     { nil if absent }
    function Contains(const AName: string): Boolean;
    { Detach a member and return it (nil if absent). }
    function Extract(const AName: string): TTOMLData;
    { Detach and discard a member.  True if it existed. }
    function Remove(const AName: string): Boolean;
    procedure Delete(AIndex: Int);
    procedure Clear;

    { The member as a table / array; nil if absent or of another kind. }
    function FindTable(const AName: string): TTOMLTable;
    function FindArray(const AName: string): TTOMLArray;
    { The member table, created (and appended) when absent.  Raises
      ETOMLError when AName holds a value that is not a table. }
    function EnsureTable(const AName: string): TTOMLTable;

    { Typed reads: False / ADefault when absent or of another kind.
      Strings also yield date-time text; floats also accept integers. }
    function TryGetString(const AName: string; out AValue: string): Boolean;
    function TryGetInt64(const AName: string; out AValue: Int64): Boolean;
    function TryGetFloat(const AName: string; out AValue: Float64): Boolean;
    function TryGetBoolean(const AName: string; out AValue: Boolean): Boolean;
    function GetString(const AName: string; const ADefault: string): string;
    function GetInt64(const AName: string; ADefault: Int64): Int64;
    function GetFloat(const AName: string; ADefault: Float64): Float64;
    function GetBoolean(const AName: string; ADefault: Boolean): Boolean;

    function GetByName(const AName: string): TTOMLData;
    function GetName(AIndex: Int): string;
    function GetItem(AIndex: Int): TTOMLData;
    property Values[AName: string]: TTOMLData read GetByName; default;
    property Names[AIndex: Int]: string read GetName;
    property ItemsByIndex[AIndex: Int]: TTOMLData read GetItem;
    { Written as an inline table rather than as a [section]. }
    property IsInline: Boolean read FInline write FInline;
  end;

{ Serialise a document.  Equivalent to ATable.AsTOML. }
function AsTOML(ATable: TTOMLTable): string;

implementation

{ True when AData would be written as a [section] or [[section]]. }
function IsSectionValue(AData: TTOMLData): Boolean;
begin
  if AData is TTOMLTable then
    Result := not TTOMLTable(AData).IsInline
  else if AData is TTOMLArray then
    Result := TTOMLArray(AData).IsArrayOfTables()
  else
    Result := False;
end;

function ExtendPath(const APath: TTOMLKeyPath; const AName: string): TTOMLKeyPath;
var
  I: Int;
begin
  SetLength(Result, Length(APath) + 1);
  I := 0;
  while I < Length(APath) do
  begin
    Result[I] := APath[I];
    I := I + 1;
  end;
  Result[Length(APath)] := AName;
end;

{ ------------------------------------------------------------------ }
{ TTOMLData                                                          }
{ ------------------------------------------------------------------ }

function TTOMLData.GetCount: Int;
begin
  Result := 0;
end;

function TTOMLData.GetAsString: string;
begin
  Result := '';
end;

function TTOMLData.GetAsInt64: Int64;
begin
  Result := 0;
end;

function TTOMLData.GetAsFloat: Float64;
begin
  Result := 0.0;
end;

function TTOMLData.GetAsBoolean: Boolean;
begin
  Result := False;
end;

function TTOMLData.IsString: Boolean;
begin
  Result := GetTOMLType() = ttString;
end;

function TTOMLData.IsInteger: Boolean;
begin
  Result := GetTOMLType() = ttInteger;
end;

function TTOMLData.IsFloat: Boolean;
begin
  Result := GetTOMLType() = ttFloat;
end;

function TTOMLData.IsBoolean: Boolean;
begin
  Result := GetTOMLType() = ttBoolean;
end;

function TTOMLData.IsDateTime: Boolean;
var
  K: TTOMLType;
begin
  K := GetTOMLType();
  Result := (K = ttOffsetDateTime) or (K = ttLocalDateTime) or
    (K = ttLocalDate) or (K = ttLocalTime);
end;

function TTOMLData.IsArray: Boolean;
begin
  Result := GetTOMLType() = ttArray;
end;

function TTOMLData.IsTable: Boolean;
begin
  Result := GetTOMLType() = ttTable;
end;

function TTOMLData.AsTOML: string;
var
  W: TTOMLWriter;
begin
  W := TTOMLWriter.Create();
  WriteValue(W);
  Result := W.ToString();
  W.Free();
end;

{ ------------------------------------------------------------------ }
{ TTOMLString                                                        }
{ ------------------------------------------------------------------ }

constructor TTOMLString.Create(const AValue: string);
begin
  FValue := AValue;
end;

function TTOMLString.GetTOMLType: TTOMLType;
begin
  Result := ttString;
end;

function TTOMLString.GetAsString: string;
begin
  Result := FValue;
end;

procedure TTOMLString.WriteValue(AWriter: TTOMLWriter);
begin
  AWriter.WriteStringValue(FValue);
end;

{ ------------------------------------------------------------------ }
{ TTOMLInteger                                                       }
{ ------------------------------------------------------------------ }

constructor TTOMLInteger.Create(AValue: Int64);
begin
  FValue := AValue;
  FText := IntToStr(AValue);
end;

constructor TTOMLInteger.CreateText(const AText: string; AValue: Int64);
begin
  FValue := AValue;
  FText := AText;
end;

procedure TTOMLInteger.SetValue(AValue: Int64);
begin
  FValue := AValue;
  FText := IntToStr(AValue);
end;

function TTOMLInteger.GetTOMLType: TTOMLType;
begin
  Result := ttInteger;
end;

function TTOMLInteger.GetAsString: string;
begin
  Result := FText;
end;

function TTOMLInteger.GetAsInt64: Int64;
begin
  Result := FValue;
end;

function TTOMLInteger.GetAsFloat: Float64;
begin
  Result := FValue;
end;

function TTOMLInteger.GetAsBoolean: Boolean;
begin
  Result := FValue <> 0;
end;

procedure TTOMLInteger.WriteValue(AWriter: TTOMLWriter);
begin
  AWriter.WriteRaw(FText);
end;

{ ------------------------------------------------------------------ }
{ TTOMLFloat                                                         }
{ ------------------------------------------------------------------ }

constructor TTOMLFloat.Create(AValue: Float64);
begin
  FValue := AValue;
  FText := TOMLFormatFloat(AValue);
end;

constructor TTOMLFloat.CreateText(const AText: string; AValue: Float64);
begin
  FValue := AValue;
  FText := AText;
end;

procedure TTOMLFloat.SetValue(AValue: Float64);
begin
  FValue := AValue;
  FText := TOMLFormatFloat(AValue);
end;

function TTOMLFloat.GetTOMLType: TTOMLType;
begin
  Result := ttFloat;
end;

function TTOMLFloat.GetAsString: string;
begin
  Result := FText;
end;

function TTOMLFloat.GetAsInt64: Int64;
begin
  Result := Trunc(FValue);
end;

function TTOMLFloat.GetAsFloat: Float64;
begin
  Result := FValue;
end;

function TTOMLFloat.GetAsBoolean: Boolean;
begin
  Result := FValue <> 0.0;
end;

procedure TTOMLFloat.WriteValue(AWriter: TTOMLWriter);
begin
  AWriter.WriteRaw(FText);
end;

{ ------------------------------------------------------------------ }
{ TTOMLBoolean                                                       }
{ ------------------------------------------------------------------ }

constructor TTOMLBoolean.Create(AValue: Boolean);
begin
  FValue := AValue;
end;

function TTOMLBoolean.GetTOMLType: TTOMLType;
begin
  Result := ttBoolean;
end;

function TTOMLBoolean.GetAsString: string;
begin
  if FValue then Result := 'true' else Result := 'false';
end;

function TTOMLBoolean.GetAsInt64: Int64;
begin
  if FValue then Result := 1 else Result := 0;
end;

function TTOMLBoolean.GetAsBoolean: Boolean;
begin
  Result := FValue;
end;

procedure TTOMLBoolean.WriteValue(AWriter: TTOMLWriter);
begin
  AWriter.WriteBoolValue(FValue);
end;

{ ------------------------------------------------------------------ }
{ TTOMLDateTime                                                      }
{ ------------------------------------------------------------------ }

constructor TTOMLDateTime.Create(AKind: TTOMLType; const AText: string);
begin
  FKind := AKind;
  FText := AText;
end;

function TTOMLDateTime.GetTOMLType: TTOMLType;
begin
  Result := FKind;
end;

function TTOMLDateTime.GetAsString: string;
begin
  Result := FText;
end;

procedure TTOMLDateTime.WriteValue(AWriter: TTOMLWriter);
begin
  AWriter.WriteRaw(FText);
end;

{ ------------------------------------------------------------------ }
{ TTOMLArray                                                         }
{ ------------------------------------------------------------------ }

function TTOMLArray.GetTOMLType: TTOMLType;
begin
  Result := ttArray;
end;

function TTOMLArray.GetCount: Int;
begin
  Result := Length(FItems);
end;

function TTOMLArray.GetItem(AIndex: Int): TTOMLData;
begin
  Result := FItems[AIndex];
end;

function TTOMLArray.Add(AValue: TTOMLData): Int;
begin
  SetLength(FItems, Length(FItems) + 1);
  FItems[Length(FItems) - 1] := AValue;
  Result := Length(FItems) - 1;
end;

function TTOMLArray.Add(const AValue: string): Int;
begin
  Result := Add(TTOMLString.Create(AValue));
end;

function TTOMLArray.Add(AValue: Int64): Int;
begin
  Result := Add(TTOMLInteger.Create(AValue));
end;

function TTOMLArray.Add(AValue: Boolean): Int;
begin
  Result := Add(TTOMLBoolean.Create(AValue));
end;

function TTOMLArray.Add(AValue: Float64): Int;
begin
  Result := Add(TTOMLFloat.Create(AValue));
end;

function TTOMLArray.Extract(AIndex: Int): TTOMLData;
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

procedure TTOMLArray.Delete(AIndex: Int);
var
  Gone: TTOMLData;
begin
  Gone := Extract(AIndex);   { dropping the local ref lets ARC free it }
end;

procedure TTOMLArray.Clear;
begin
  SetLength(FItems, 0);
end;

function TTOMLArray.IsArrayOfTables: Boolean;
var
  I: Int;
begin
  Result := Length(FItems) > 0;
  I := 0;
  while Result and (I < Length(FItems)) do
  begin
    Result := (FItems[I] is TTOMLTable) and not TTOMLTable(FItems[I]).IsInline;
    I := I + 1;
  end;
end;

procedure TTOMLArray.WriteValue(AWriter: TTOMLWriter);
var
  I: Int;
begin
  AWriter.BeginArray();
  I := 0;
  while I < Length(FItems) do
  begin
    FItems[I].WriteValue(AWriter);
    I := I + 1;
  end;
  AWriter.EndArray();
end;

{ ------------------------------------------------------------------ }
{ TTOMLTable                                                         }
{ ------------------------------------------------------------------ }

function TTOMLTable.GetTOMLType: TTOMLType;
begin
  Result := ttTable;
end;

function TTOMLTable.GetCount: Int;
begin
  Result := Length(FValues);
end;

function TTOMLTable.IndexOfName(const AName: string): Int;
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

procedure TTOMLTable.RemoveIndex(AIndex: Int);
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

function TTOMLTable.Add(const AName: string; AValue: TTOMLData): Int;
begin
  if IndexOfName(AName) >= 0 then
    raise ETOMLError.Create('duplicate TOML key ' + TOMLFormatKey(AName));
  SetLength(FNames, Length(FNames) + 1);
  SetLength(FValues, Length(FValues) + 1);
  FNames[Length(FNames) - 1] := AName;
  FValues[Length(FValues) - 1] := AValue;
  Result := Length(FValues) - 1;
end;

procedure TTOMLTable.Put(const AName: string; AValue: TTOMLData);
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  if Idx >= 0 then
    FValues[Idx] := AValue
  else
    Add(AName, AValue);
end;

procedure TTOMLTable.Put(const AName: string; const AValue: string);
begin
  Put(AName, TTOMLString.Create(AValue));
end;

procedure TTOMLTable.Put(const AName: string; AValue: Int64);
begin
  Put(AName, TTOMLInteger.Create(AValue));
end;

procedure TTOMLTable.Put(const AName: string; AValue: Boolean);
begin
  Put(AName, TTOMLBoolean.Create(AValue));
end;

procedure TTOMLTable.Put(const AName: string; AValue: Float64);
begin
  Put(AName, TTOMLFloat.Create(AValue));
end;

function TTOMLTable.Find(const AName: string): TTOMLData;
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  if Idx < 0 then Result := nil else Result := FValues[Idx];
end;

function TTOMLTable.Contains(const AName: string): Boolean;
begin
  Result := IndexOfName(AName) >= 0;
end;

function TTOMLTable.Extract(const AName: string): TTOMLData;
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

function TTOMLTable.Remove(const AName: string): Boolean;
var
  Idx: Int;
begin
  Idx := IndexOfName(AName);
  Result := Idx >= 0;
  if Result then
    RemoveIndex(Idx);
end;

procedure TTOMLTable.Delete(AIndex: Int);
begin
  RemoveIndex(AIndex);
end;

procedure TTOMLTable.Clear;
begin
  SetLength(FNames, 0);
  SetLength(FValues, 0);
end;

function TTOMLTable.FindTable(const AName: string): TTOMLTable;
var
  D: TTOMLData;
begin
  D := Find(AName);
  if (D <> nil) and (D is TTOMLTable) then
    Result := TTOMLTable(D)
  else
    Result := nil;
end;

function TTOMLTable.FindArray(const AName: string): TTOMLArray;
var
  D: TTOMLData;
begin
  D := Find(AName);
  if (D <> nil) and (D is TTOMLArray) then
    Result := TTOMLArray(D)
  else
    Result := nil;
end;

function TTOMLTable.EnsureTable(const AName: string): TTOMLTable;
var
  D: TTOMLData;
begin
  D := Find(AName);
  if D = nil then
  begin
    Result := TTOMLTable.Create();
    Add(AName, Result);
  end
  else if D is TTOMLTable then
    Result := TTOMLTable(D)
  else
    raise ETOMLError.Create('TOML key ' + TOMLFormatKey(AName) +
      ' holds a value that is not a table');
end;

function TTOMLTable.TryGetString(const AName: string; out AValue: string): Boolean;
var
  D: TTOMLData;
begin
  D := Find(AName);
  Result := (D <> nil) and (D.IsString() or D.IsDateTime());
  if Result then
    AValue := D.AsString
  else
    AValue := '';
end;

function TTOMLTable.TryGetInt64(const AName: string; out AValue: Int64): Boolean;
var
  D: TTOMLData;
begin
  D := Find(AName);
  Result := (D <> nil) and D.IsInteger();
  if Result then
    AValue := D.AsInt64
  else
    AValue := 0;
end;

function TTOMLTable.TryGetFloat(const AName: string; out AValue: Float64): Boolean;
var
  D: TTOMLData;
begin
  D := Find(AName);
  Result := (D <> nil) and (D.IsFloat() or D.IsInteger());
  if Result then
    AValue := D.AsFloat
  else
    AValue := 0.0;
end;

function TTOMLTable.TryGetBoolean(const AName: string; out AValue: Boolean): Boolean;
var
  D: TTOMLData;
begin
  D := Find(AName);
  Result := (D <> nil) and D.IsBoolean();
  if Result then
    AValue := D.AsBoolean
  else
    AValue := False;
end;

function TTOMLTable.GetString(const AName: string; const ADefault: string): string;
begin
  if not TryGetString(AName, Result) then
    Result := ADefault;
end;

function TTOMLTable.GetInt64(const AName: string; ADefault: Int64): Int64;
begin
  if not TryGetInt64(AName, Result) then
    Result := ADefault;
end;

function TTOMLTable.GetFloat(const AName: string; ADefault: Float64): Float64;
begin
  if not TryGetFloat(AName, Result) then
    Result := ADefault;
end;

function TTOMLTable.GetBoolean(const AName: string; ADefault: Boolean): Boolean;
begin
  if not TryGetBoolean(AName, Result) then
    Result := ADefault;
end;

function TTOMLTable.GetByName(const AName: string): TTOMLData;
begin
  Result := Find(AName);
end;

function TTOMLTable.GetName(AIndex: Int): string;
begin
  Result := FNames[AIndex];
end;

function TTOMLTable.GetItem(AIndex: Int): TTOMLData;
begin
  Result := FValues[AIndex];
end;

function TTOMLTable.HasPlainEntries: Boolean;
var
  I: Int;
begin
  Result := False;
  I := 0;
  while I < Length(FValues) do
  begin
    if not IsSectionValue(FValues[I]) then
    begin
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
end;

procedure TTOMLTable.WriteValue(AWriter: TTOMLWriter);
var
  I: Int;
begin
  AWriter.BeginInlineTable();
  I := 0;
  while I < Length(FValues) do
  begin
    AWriter.WriteKey(FNames[I]);
    FValues[I].WriteValue(AWriter);
    I := I + 1;
  end;
  AWriter.EndInlineTable();
end;

{ Plain key/value pairs first, then the sections below APath.  A sub-table
  gets a header only when it has plain entries of its own or is empty: a
  table holding nothing but sections is defined implicitly by theirs. }
procedure TTOMLTable.WriteBody(AWriter: TTOMLWriter; const APath: TTOMLKeyPath);
var
  I, J: Int;
  V: TTOMLData;
  Sub: TTOMLTable;
  Arr: TTOMLArray;
  SubPath: TTOMLKeyPath;
begin
  I := 0;
  while I < Length(FValues) do
  begin
    V := FValues[I];
    if not IsSectionValue(V) then
    begin
      AWriter.WriteKey(FNames[I]);
      V.WriteValue(AWriter);
    end;
    I := I + 1;
  end;
  I := 0;
  while I < Length(FValues) do
  begin
    V := FValues[I];
    if IsSectionValue(V) then
    begin
      SubPath := ExtendPath(APath, FNames[I]);
      if V is TTOMLTable then
      begin
        Sub := TTOMLTable(V);
        if Sub.HasPlainEntries() or (Sub.Count = 0) then
          AWriter.BeginTable(SubPath);
        Sub.WriteBody(AWriter, SubPath);
      end
      else
      begin
        Arr := TTOMLArray(V);
        J := 0;
        while J < Arr.Count do
        begin
          AWriter.BeginArrayTable(SubPath);
          TTOMLTable(Arr[J]).WriteBody(AWriter, SubPath);
          J := J + 1;
        end;
      end;
    end;
    I := I + 1;
  end;
end;

procedure TTOMLTable.WriteDocument(AWriter: TTOMLWriter);
var
  Root: TTOMLKeyPath;
begin
  SetLength(Root, 0);
  WriteBody(AWriter, Root);
end;

function TTOMLTable.AsTOML: string;
var
  W: TTOMLWriter;
begin
  W := TTOMLWriter.Create();
  WriteDocument(W);
  Result := W.ToString();
  W.Free();
end;

{ ------------------------------------------------------------------ }
{ free functions                                                     }
{ ------------------------------------------------------------------ }

function AsTOML(ATable: TTOMLTable): string;
begin
  Result := ATable.AsTOML();
end;

end.
