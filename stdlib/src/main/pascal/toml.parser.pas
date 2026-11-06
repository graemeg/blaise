{
  Blaise stdlib - TOML parser
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - TOML 1.0 parser.

  TTOMLParser reads a whole TOML document into the Toml.Types tree and
  returns its root table.  It implements TOML 1.0.0:

    - basic, literal and multi-line strings, with every escape
      (\b \t \n \f \r \" \\ \uXXXX \UXXXXXXXX) and line-ending backslashes;
    - integers in decimal, 0x hex, 0o octal and 0b binary, with underscores,
      range-checked to Int64;
    - floats with fraction and/or exponent, and inf / nan with either sign;
    - booleans; offset and local date-times, local dates and local times,
      validated and kept as their text (TTOMLDateTime);
    - arrays (multi-line, comments, trailing comma) and inline tables;
    - [table] and [a.b] headers, dotted keys, bare / quoted / literal keys,
      and [[array of tables]].

  The definition rules are enforced: a key may not be set twice, a table may
  not be defined twice, a table created by dotted keys may not get a header,
  a header-defined table may not be extended by dotted keys from its parent,
  inline tables and static arrays are sealed.

  Malformed input raises ETOMLParseError, whose Line and Column (both from 1;
  the column counts bytes) locate the error; the message ends with
  'at line L, column C'.
}

unit Toml.Parser;

interface

uses
  SysUtils, StrUtils, Toml.Types;

type
  ETOMLParseError = class(ETOMLError)
  private
    FLine:   Int;
    FColumn: Int;
  public
    constructor CreateAt(const AMsg: string; ALine, AColumn: Int);
    property Line: Int read FLine;
    property Column: Int read FColumn;
  end;

  TTOMLParser = class
  private
    FText:    string;
    FPos:     Int;
    FLen:     Int;
    FRoot:    TTOMLTable;
    FCurrent: TTOMLTable;              { the table the last header selected }
    { Definition bookkeeping (identity lists; documents are small). }
    FHeaderTables: array of TTOMLTable;   { defined by [header] / [[header]] }
    FDottedTables: array of TTOMLTable;   { created by dotted keys }
    FTableArrays:  array of TTOMLArray;   { created by [[header]] }
    procedure FailAt(APos: Int; const AMsg: string);
    procedure Fail(const AMsg: string);
    function  Peek: Int;                  { current byte, or -1 at end }
    function  PeekAt(AOffset: Int): Int;
    function  IsDigitAt(AOffset: Int): Boolean;
    procedure SkipSpaces;                 { spaces and tabs }
    procedure SkipComment;                { '#' to end of line, not the EOL }
    { Spaces, tabs, newlines and comments (inside arrays). }
    procedure SkipBlankLines;
    procedure ExpectLineEnd;
    function  AtNewline: Boolean;
    procedure ConsumeNewline;

    function  InHeaderTables(T: TTOMLTable): Boolean;
    function  InDottedTables(T: TTOMLTable): Boolean;
    function  InTableArrays(A: TTOMLArray): Boolean;

    function  ParseKey: TTOMLKeyPath;
    function  ParseBareKey: string;
    procedure ParseHeader;
    procedure ParseKeyValue(ATable: TTOMLTable);
    procedure InsertKeyValue(ATable: TTOMLTable; const AKeys: TTOMLKeyPath;
      AValue: TTOMLData; AKeyPos: Int);

    function  ParseValue: TTOMLData;
    function  ParseArray: TTOMLArray;
    function  ParseInlineTable: TTOMLTable;
    function  ParseBasicString: string;
    function  ParseLiteralString: string;
    function  ParseMultiLineBasicString: string;
    function  ParseMultiLineLiteralString: string;
    procedure ParseEscape(ASB: TStringBuilder);
    procedure CheckStringByte(C: Int);
    function  ParseNumber: TTOMLData;
    function  ParseDateTime: TTOMLData;
    function  ReadDigits(ACount: Int; const AWhat: string): Int;
    procedure ParseTimePart;
  public
    constructor Create(const AText: string);
    { Parse the whole document; raises ETOMLParseError on malformed input. }
    function Parse: TTOMLTable;
  end;

implementation

const
  MaxInt64Value = 9223372036854775807;

{ ------------------------------------------------------------------ }
{ ETOMLParseError                                                    }
{ ------------------------------------------------------------------ }

constructor ETOMLParseError.CreateAt(const AMsg: string; ALine, AColumn: Int);
begin
  inherited Create(AMsg + ' at line ' + IntToStr(ALine) + ', column ' +
    IntToStr(AColumn));
  FLine := ALine;
  FColumn := AColumn;
end;

{ ------------------------------------------------------------------ }
{ helpers                                                            }
{ ------------------------------------------------------------------ }

function TPIsDigit(C: Int): Boolean;
begin
  Result := (C >= Ord('0')) and (C <= Ord('9'));
end;

function TPHexVal(C: Int): Int;
begin
  if (C >= Ord('0')) and (C <= Ord('9')) then
    Result := C - Ord('0')
  else if (C >= Ord('a')) and (C <= Ord('f')) then
    Result := C - Ord('a') + 10
  else if (C >= Ord('A')) and (C <= Ord('F')) then
    Result := C - Ord('A') + 10
  else
    Result := -1;
end;

function TPIsBareKeyByte(C: Int): Boolean;
begin
  Result := ((C >= Ord('A')) and (C <= Ord('Z'))) or
    ((C >= Ord('a')) and (C <= Ord('z'))) or TPIsDigit(C) or
    (C = Ord('_')) or (C = Ord('-'));
end;

{ Append codepoint ACP to ASB as UTF-8 bytes. }
procedure TPAppendUTF8(ASB: TStringBuilder; ACP: Int);
begin
  if ACP < $80 then
    ASB.AppendByte(ACP)
  else if ACP < $800 then
  begin
    ASB.AppendByte($C0 + (ACP div $40));
    ASB.AppendByte($80 + (ACP mod $40));
  end
  else if ACP < $10000 then
  begin
    ASB.AppendByte($E0 + (ACP div $1000));
    ASB.AppendByte($80 + ((ACP div $40) mod $40));
    ASB.AppendByte($80 + (ACP mod $40));
  end
  else
  begin
    ASB.AppendByte($F0 + (ACP div $40000));
    ASB.AppendByte($80 + ((ACP div $1000) mod $40));
    ASB.AppendByte($80 + ((ACP div $40) mod $40));
    ASB.AppendByte($80 + (ACP mod $40));
  end;
end;

{ True when S (a run of digits valid in ABase, plus underscores) is
  non-empty, starts and ends with a digit and has no doubled underscore. }
function TPValidDigitRun(const S: string; ABase: Int): Boolean;
var
  I, C: Int;
  PrevUnderscore: Boolean;
begin
  Result := Length(S) > 0;
  PrevUnderscore := True;    { a leading underscore is rejected }
  I := 0;
  while Result and (I < Length(S)) do
  begin
    C := Byte(S[I]);
    if C = Ord('_') then
    begin
      Result := not PrevUnderscore;
      PrevUnderscore := True;
    end
    else
    begin
      Result := (TPHexVal(C) >= 0) and (TPHexVal(C) < ABase);
      PrevUnderscore := False;
    end;
    I := I + 1;
  end;
  if Result then
    Result := not PrevUnderscore;
end;

function TPStripUnderscores(const S: string): string;
var
  SB: TStringBuilder;
  I: Int;
begin
  SB := TStringBuilder.Create();
  I := 0;
  while I < Length(S) do
  begin
    if Byte(S[I]) <> Ord('_') then
      SB.AppendByte(Byte(S[I]));
    I := I + 1;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TPIsLeapYear(Y: Int): Boolean;
begin
  Result := ((Y mod 4 = 0) and (Y mod 100 <> 0)) or (Y mod 400 = 0);
end;

function TPDaysInMonth(Y, M: Int): Int;
begin
  if M = 2 then
  begin
    if TPIsLeapYear(Y) then Result := 29 else Result := 28;
  end
  else if (M = 4) or (M = 6) or (M = 9) or (M = 11) then
    Result := 30
  else
    Result := 31;
end;

{ ------------------------------------------------------------------ }
{ TTOMLParser - low level                                            }
{ ------------------------------------------------------------------ }

constructor TTOMLParser.Create(const AText: string);
begin
  FText := AText;
  FPos := 0;
  FLen := Length(AText);
end;

procedure TTOMLParser.FailAt(APos: Int; const AMsg: string);
var
  I, Line, LineStart: Int;
begin
  if APos > FLen then
    APos := FLen;
  Line := 1;
  LineStart := 0;
  I := 0;
  while I < APos do
  begin
    if Byte(FText[I]) = 10 then
    begin
      Line := Line + 1;
      LineStart := I + 1;
    end;
    I := I + 1;
  end;
  raise ETOMLParseError.CreateAt(AMsg, Line, APos - LineStart + 1);
end;

procedure TTOMLParser.Fail(const AMsg: string);
begin
  FailAt(FPos, AMsg);
end;

function TTOMLParser.Peek: Int;
begin
  if FPos < FLen then
    Result := Byte(FText[FPos])
  else
    Result := -1;
end;

function TTOMLParser.PeekAt(AOffset: Int): Int;
begin
  if FPos + AOffset < FLen then
    Result := Byte(FText[FPos + AOffset])
  else
    Result := -1;
end;

function TTOMLParser.IsDigitAt(AOffset: Int): Boolean;
begin
  Result := TPIsDigit(PeekAt(AOffset));
end;

procedure TTOMLParser.SkipSpaces;
var
  C: Int;
begin
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if (C = 32) or (C = 9) then
      FPos := FPos + 1
    else
      Exit;
  end;
end;

procedure TTOMLParser.SkipComment;
var
  C: Int;
begin
  if Peek() <> Ord('#') then
    Exit;
  FPos := FPos + 1;
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if (C = 10) or ((C = 13) and (PeekAt(1) = 10)) then
      Exit;
    if ((C < 32) and (C <> 9)) or (C = 127) then
      Fail('control character in comment');
    FPos := FPos + 1;
  end;
end;

function TTOMLParser.AtNewline: Boolean;
begin
  Result := (Peek() = 10) or (Peek() = 13);
end;

procedure TTOMLParser.ConsumeNewline;
begin
  if Peek() = 10 then
    FPos := FPos + 1
  else if (Peek() = 13) and (PeekAt(1) = 10) then
    FPos := FPos + 2
  else
    Fail('carriage return not followed by a line feed');
end;

procedure TTOMLParser.SkipBlankLines;
begin
  while True do
  begin
    SkipSpaces();
    if Peek() = Ord('#') then
      SkipComment();
    if AtNewline() then
      ConsumeNewline()
    else
      Exit;
  end;
end;

{ After a key/value pair or header: optional comment, then end of line. }
procedure TTOMLParser.ExpectLineEnd;
begin
  SkipSpaces();
  SkipComment();
  if FPos >= FLen then
    Exit;
  if AtNewline() then
    ConsumeNewline()
  else
    Fail('expected end of line');
end;

function TTOMLParser.InHeaderTables(T: TTOMLTable): Boolean;
var
  I: Int;
begin
  Result := False;
  I := 0;
  while I < Length(FHeaderTables) do
  begin
    if FHeaderTables[I] = T then
    begin
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
end;

function TTOMLParser.InDottedTables(T: TTOMLTable): Boolean;
var
  I: Int;
begin
  Result := False;
  I := 0;
  while I < Length(FDottedTables) do
  begin
    if FDottedTables[I] = T then
    begin
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
end;

function TTOMLParser.InTableArrays(A: TTOMLArray): Boolean;
var
  I: Int;
begin
  Result := False;
  I := 0;
  while I < Length(FTableArrays) do
  begin
    if FTableArrays[I] = A then
    begin
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
end;

{ ------------------------------------------------------------------ }
{ TTOMLParser - document structure                                   }
{ ------------------------------------------------------------------ }

function TTOMLParser.Parse: TTOMLTable;
var
  C: Int;
begin
  FRoot := TTOMLTable.Create();
  FCurrent := FRoot;
  while True do
  begin
    SkipSpaces();
    if FPos >= FLen then
      Break;
    C := Peek();
    if C = Ord('#') then
      SkipComment()
    else if AtNewline() then
    begin
      ConsumeNewline();
      Continue;
    end
    else if C = Ord('[') then
      ParseHeader()
    else
      ParseKeyValue(FCurrent);
    ExpectLineEnd();
  end;
  Result := FRoot;
  FCurrent := nil;
  FRoot := nil;
  SetLength(FHeaderTables, 0);
  SetLength(FDottedTables, 0);
  SetLength(FTableArrays, 0);
end;

function TTOMLParser.ParseBareKey: string;
var
  Start: Int;
begin
  Start := FPos;
  while (FPos < FLen) and TPIsBareKeyByte(Byte(FText[FPos])) do
    FPos := FPos + 1;
  if FPos = Start then
    Fail('expected a key');
  Result := Copy(FText, Start, FPos - Start);
end;

{ key ( '.' key )* with optional spaces around the dots. }
function TTOMLParser.ParseKey: TTOMLKeyPath;
var
  C: Int;
  Part: string;
begin
  SetLength(Result, 0);
  while True do
  begin
    SkipSpaces();
    C := Peek();
    if C = Ord('"') then
    begin
      if (PeekAt(1) = Ord('"')) and (PeekAt(2) = Ord('"')) then
        Fail('multi-line string is not allowed as a key');
      Part := ParseBasicString();
    end
    else if C = Ord('''') then
    begin
      if (PeekAt(1) = Ord('''')) and (PeekAt(2) = Ord('''')) then
        Fail('multi-line string is not allowed as a key');
      Part := ParseLiteralString();
    end
    else
      Part := ParseBareKey();
    SetLength(Result, Length(Result) + 1);
    Result[Length(Result) - 1] := Part;
    SkipSpaces();
    if Peek() = Ord('.') then
      FPos := FPos + 1
    else
      Break;
  end;
end;

procedure TTOMLParser.ParseHeader;
var
  IsArray: Boolean;
  StartPos, I: Int;
  Keys: TTOMLKeyPath;
  T, NewT: TTOMLTable;
  D: TTOMLData;
  Arr: TTOMLArray;
  Name: string;
begin
  StartPos := FPos;
  IsArray := PeekAt(1) = Ord('[');
  if IsArray then
    FPos := FPos + 2
  else
    FPos := FPos + 1;
  SkipSpaces();
  if Peek() = Ord(']') then
    Fail('empty table header');
  Keys := ParseKey();
  SkipSpaces();
  if Peek() <> Ord(']') then
    Fail('expected '']'' to close the table header');
  FPos := FPos + 1;
  if IsArray then
  begin
    if Peek() <> Ord(']') then
      Fail('expected '']]'' to close the array-of-tables header');
    FPos := FPos + 1;
  end;

  { Walk (creating implicitly) every key but the last. }
  T := FRoot;
  I := 0;
  while I < Length(Keys) - 1 do
  begin
    D := T.Find(Keys[I]);
    if D = nil then
    begin
      NewT := TTOMLTable.Create();
      T.Add(Keys[I], NewT);
      T := NewT;
    end
    else if D is TTOMLTable then
    begin
      if TTOMLTable(D).IsInline then
        FailAt(StartPos, 'cannot extend inline table ' + Keys[I]);
      T := TTOMLTable(D);
    end
    else if (D is TTOMLArray) and InTableArrays(TTOMLArray(D)) then
      T := TTOMLTable(TTOMLArray(D)[TTOMLArray(D).Count - 1])
    else
      FailAt(StartPos, 'key ' + Keys[I] + ' is not a table');
    I := I + 1;
  end;

  Name := Keys[Length(Keys) - 1];
  D := T.Find(Name);
  if IsArray then
  begin
    if D = nil then
    begin
      Arr := TTOMLArray.Create();
      T.Add(Name, Arr);
      SetLength(FTableArrays, Length(FTableArrays) + 1);
      FTableArrays[Length(FTableArrays) - 1] := Arr;
    end
    else if (D is TTOMLArray) and InTableArrays(TTOMLArray(D)) then
      Arr := TTOMLArray(D)
    else
    begin
      Arr := nil;
      FailAt(StartPos, 'key ' + Name + ' is already defined and is not an ' +
        'array of tables');
    end;
    NewT := TTOMLTable.Create();
    Arr.Add(NewT);
  end
  else
  begin
    if D = nil then
    begin
      NewT := TTOMLTable.Create();
      T.Add(Name, NewT);
    end
    else if (D is TTOMLTable) and not TTOMLTable(D).IsInline and
            not InHeaderTables(TTOMLTable(D)) and
            not InDottedTables(TTOMLTable(D)) then
      NewT := TTOMLTable(D)          { defined implicitly before; now explicitly }
    else
    begin
      NewT := nil;
      FailAt(StartPos, 'table ' + Name + ' is already defined');
    end;
  end;
  SetLength(FHeaderTables, Length(FHeaderTables) + 1);
  FHeaderTables[Length(FHeaderTables) - 1] := NewT;
  FCurrent := NewT;
end;

procedure TTOMLParser.ParseKeyValue(ATable: TTOMLTable);
var
  KeyPos: Int;
  Keys: TTOMLKeyPath;
  V: TTOMLData;
begin
  KeyPos := FPos;
  Keys := ParseKey();
  SkipSpaces();
  if Peek() <> Ord('=') then
    Fail('expected ''='' after a key');
  FPos := FPos + 1;
  SkipSpaces();
  V := ParseValue();
  InsertKeyValue(ATable, Keys, V, KeyPos);
end;

procedure TTOMLParser.InsertKeyValue(ATable: TTOMLTable;
  const AKeys: TTOMLKeyPath; AValue: TTOMLData; AKeyPos: Int);
var
  T, NewT: TTOMLTable;
  D: TTOMLData;
  I: Int;
  Name: string;
begin
  T := ATable;
  I := 0;
  while I < Length(AKeys) - 1 do
  begin
    D := T.Find(AKeys[I]);
    if D = nil then
    begin
      NewT := TTOMLTable.Create();
      T.Add(AKeys[I], NewT);
      SetLength(FDottedTables, Length(FDottedTables) + 1);
      FDottedTables[Length(FDottedTables) - 1] := NewT;
      T := NewT;
    end
    else if (D is TTOMLTable) and not TTOMLTable(D).IsInline and
            InDottedTables(TTOMLTable(D)) then
      T := TTOMLTable(D)
    else
      FailAt(AKeyPos, 'cannot add dotted key below ' + AKeys[I] +
        ': it is already defined');
    I := I + 1;
  end;
  Name := AKeys[Length(AKeys) - 1];
  if T.Contains(Name) then
    FailAt(AKeyPos, 'duplicate key ' + Name);
  T.Add(Name, AValue);
end;

{ ------------------------------------------------------------------ }
{ TTOMLParser - values                                               }
{ ------------------------------------------------------------------ }

function TTOMLParser.ParseValue: TTOMLData;
var
  C: Int;
begin
  C := Peek();
  if C = Ord('"') then
  begin
    if (PeekAt(1) = Ord('"')) and (PeekAt(2) = Ord('"')) then
      Result := TTOMLString.Create(ParseMultiLineBasicString())
    else
      Result := TTOMLString.Create(ParseBasicString());
  end
  else if C = Ord('''') then
  begin
    if (PeekAt(1) = Ord('''')) and (PeekAt(2) = Ord('''')) then
      Result := TTOMLString.Create(ParseMultiLineLiteralString())
    else
      Result := TTOMLString.Create(ParseLiteralString());
  end
  else if C = Ord('[') then
    Result := ParseArray()
  else if C = Ord('{') then
    Result := ParseInlineTable()
  else if (FPos + 4 <= FLen) and (Copy(FText, FPos, 4) = 'true') and
          not TPIsBareKeyByte(PeekAt(4)) then
  begin
    FPos := FPos + 4;
    Result := TTOMLBoolean.Create(True);
  end
  else if (FPos + 5 <= FLen) and (Copy(FText, FPos, 5) = 'false') and
          not TPIsBareKeyByte(PeekAt(5)) then
  begin
    FPos := FPos + 5;
    Result := TTOMLBoolean.Create(False);
  end
  else if TPIsDigit(C) and IsDigitAt(1) and
          ((PeekAt(2) = Ord(':')) or
           (IsDigitAt(2) and IsDigitAt(3) and (PeekAt(4) = Ord('-')))) then
    Result := ParseDateTime()
  else if TPIsDigit(C) or (C = Ord('+')) or (C = Ord('-')) or
          (C = Ord('i')) or (C = Ord('n')) then
    Result := ParseNumber()
  else
  begin
    Result := nil;
    if (C = -1) or (C = 10) or (C = 13) or (C = Ord('#')) then
      Fail('expected a value')
    else
      Fail('invalid value');
  end;
end;

function TTOMLParser.ParseArray: TTOMLArray;
var
  Arr: TTOMLArray;
begin
  Arr := TTOMLArray.Create();
  FPos := FPos + 1;          { consume '[' }
  while True do
  begin
    SkipBlankLines();
    if Peek() = Ord(']') then
    begin
      FPos := FPos + 1;
      Break;
    end;
    if FPos >= FLen then
      Fail('unterminated array');
    Arr.Add(ParseValue());
    SkipBlankLines();
    if Peek() = Ord(',') then
      FPos := FPos + 1
    else if Peek() = Ord(']') then
    begin
      FPos := FPos + 1;
      Break;
    end
    else if FPos >= FLen then
      Fail('unterminated array')
    else
      Fail('expected '','' or '']'' in array');
  end;
  Result := Arr;
end;

function TTOMLParser.ParseInlineTable: TTOMLTable;
var
  T: TTOMLTable;
begin
  T := TTOMLTable.Create();
  FPos := FPos + 1;          { consume '{' }
  SkipSpaces();
  if Peek() = Ord('}') then
    FPos := FPos + 1
  else
  begin
    while True do
    begin
      SkipSpaces();
      if AtNewline() or (FPos >= FLen) then
        Fail('inline table must be on a single line');
      ParseKeyValue(T);
      SkipSpaces();
      if Peek() = Ord(',') then
        FPos := FPos + 1
      else if Peek() = Ord('}') then
      begin
        FPos := FPos + 1;
        Break;
      end
      else if AtNewline() or (FPos >= FLen) then
        Fail('inline table must be on a single line')
      else
        Fail('expected '','' or ''}'' in inline table');
    end;
  end;
  T.IsInline := True;
  Result := T;
end;

{ A byte inside a string: control characters other than tab are not allowed
  literally. }
procedure TTOMLParser.CheckStringByte(C: Int);
begin
  if ((C < 32) and (C <> 9)) or (C = 127) then
    Fail('control character in string');
end;

procedure TTOMLParser.ParseEscape(ASB: TStringBuilder);
var
  Esc, N, K, D, CP, EscPos: Int;
begin
  EscPos := FPos;
  FPos := FPos + 1;          { consume '\' }
  Esc := Peek();
  FPos := FPos + 1;
  if Esc = Ord('b') then ASB.AppendByte(8)
  else if Esc = Ord('t') then ASB.AppendByte(9)
  else if Esc = Ord('n') then ASB.AppendByte(10)
  else if Esc = Ord('f') then ASB.AppendByte(12)
  else if Esc = Ord('r') then ASB.AppendByte(13)
  else if Esc = Ord('"') then ASB.AppendByte(Ord('"'))
  else if Esc = Ord('\') then ASB.AppendByte(Ord('\'))
  else if (Esc = Ord('u')) or (Esc = Ord('U')) then
  begin
    if Esc = Ord('u') then N := 4 else N := 8;
    CP := 0;
    K := 0;
    while K < N do
    begin
      D := TPHexVal(Peek());
      if D < 0 then
        Fail('bad hex digit in unicode escape');
      CP := CP * 16 + D;
      FPos := FPos + 1;
      K := K + 1;
    end;
    if ((CP >= $D800) and (CP <= $DFFF)) or (CP > $10FFFF) then
      FailAt(EscPos, 'unicode escape is not a scalar value');
    TPAppendUTF8(ASB, CP);
  end
  else
    FailAt(EscPos, 'invalid escape sequence');
end;

function TTOMLParser.ParseBasicString: string;
var
  SB: TStringBuilder;
  C, StartPos: Int;
begin
  StartPos := FPos;
  SB := TStringBuilder.Create();
  FPos := FPos + 1;          { consume opening '"' }
  while True do
  begin
    if (FPos >= FLen) or AtNewline() then
      FailAt(StartPos, 'unterminated string');
    C := Peek();
    if C = Ord('"') then
    begin
      FPos := FPos + 1;
      Break;
    end
    else if C = Ord('\') then
      ParseEscape(SB)
    else
    begin
      CheckStringByte(C);
      SB.AppendByte(C);
      FPos := FPos + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TTOMLParser.ParseLiteralString: string;
var
  C, StartPos, Start: Int;
begin
  StartPos := FPos;
  FPos := FPos + 1;          { consume opening quote }
  Start := FPos;
  while True do
  begin
    if (FPos >= FLen) or AtNewline() then
      FailAt(StartPos, 'unterminated string');
    C := Peek();
    if C = Ord('''') then
      Break;
    CheckStringByte(C);
    FPos := FPos + 1;
  end;
  Result := Copy(FText, Start, FPos - Start);
  FPos := FPos + 1;          { consume closing quote }
end;

function TTOMLParser.ParseMultiLineBasicString: string;
var
  SB: TStringBuilder;
  C, StartPos, Q, K, Save: Int;
  LineEnd: Boolean;
begin
  StartPos := FPos;
  SB := TStringBuilder.Create();
  FPos := FPos + 3;
  if AtNewline() then
    ConsumeNewline();        { a newline straight after the opener is trimmed }
  while True do
  begin
    if FPos >= FLen then
      FailAt(StartPos, 'unterminated multi-line string');
    C := Peek();
    if C = Ord('"') then
    begin
      Q := 0;
      while PeekAt(Q) = Ord('"') do
        Q := Q + 1;
      if Q >= 3 then
      begin
        if Q > 5 then
          Fail('too many quotes at the end of a multi-line string');
        K := 0;
        while K < Q - 3 do
        begin
          SB.AppendByte(Ord('"'));
          K := K + 1;
        end;
        FPos := FPos + Q;
        Break;
      end;
      K := 0;
      while K < Q do
      begin
        SB.AppendByte(Ord('"'));
        K := K + 1;
      end;
      FPos := FPos + Q;
    end
    else if C = Ord('\') then
    begin
      { A line-ending backslash: '\', optional spaces, then a newline. }
      Save := FPos;
      FPos := FPos + 1;
      SkipSpaces();
      LineEnd := AtNewline();
      if LineEnd then
      begin
        while (Peek() = 32) or (Peek() = 9) or AtNewline() do
        begin
          if AtNewline() then
            ConsumeNewline()
          else
            FPos := FPos + 1;
        end;
      end
      else
      begin
        FPos := Save;
        ParseEscape(SB);
      end;
    end
    else if AtNewline() then
    begin
      ConsumeNewline();
      SB.AppendByte(10);
    end
    else
    begin
      CheckStringByte(C);
      SB.AppendByte(C);
      FPos := FPos + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TTOMLParser.ParseMultiLineLiteralString: string;
var
  SB: TStringBuilder;
  C, StartPos, Q, K: Int;
begin
  StartPos := FPos;
  SB := TStringBuilder.Create();
  FPos := FPos + 3;
  if AtNewline() then
    ConsumeNewline();
  while True do
  begin
    if FPos >= FLen then
      FailAt(StartPos, 'unterminated multi-line string');
    C := Peek();
    if C = Ord('''') then
    begin
      Q := 0;
      while PeekAt(Q) = Ord('''') do
        Q := Q + 1;
      if Q >= 3 then
      begin
        if Q > 5 then
          Fail('too many quotes at the end of a multi-line string');
        K := 0;
        while K < Q - 3 do
        begin
          SB.AppendByte(Ord(''''));
          K := K + 1;
        end;
        FPos := FPos + Q;
        Break;
      end;
      K := 0;
      while K < Q do
      begin
        SB.AppendByte(Ord(''''));
        K := K + 1;
      end;
      FPos := FPos + Q;
    end
    else if AtNewline() then
    begin
      ConsumeNewline();
      SB.AppendByte(10);
    end
    else
    begin
      CheckStringByte(C);
      SB.AppendByte(C);
      FPos := FPos + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

{ Integers and floats.  The lexeme runs over the bytes a number can hold;
  it is then validated as a whole. }
function TTOMLParser.ParseNumber: TTOMLData;
var
  Start, C, I, Base, D, ExpPos: Int;
  Lex, Body, IntPart, FracPart, ExpPart, Digits: string;
  Neg, HasSign: Boolean;
  Acc: Int64;
  Z, F: Float64;
begin
  Start := FPos;
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if TPIsBareKeyByte(C) or (C = Ord('.')) or (C = Ord('+')) then
      FPos := FPos + 1
    else
      Break;
  end;
  Lex := Copy(FText, Start, FPos - Start);
  HasSign := (Length(Lex) > 0) and
    ((Byte(Lex[0]) = Ord('+')) or (Byte(Lex[0]) = Ord('-')));
  Neg := HasSign and (Byte(Lex[0]) = Ord('-'));
  if HasSign then
    Body := Copy(Lex, 1, Length(Lex) - 1)
  else
    Body := Lex;

  { inf / nan }
  if (Body = 'inf') or (Body = 'nan') then
  begin
    Z := 0.0;
    if Body = 'nan' then
      F := Z / Z
    else if Neg then
      F := -1.0 / Z
    else
      F := 1.0 / Z;
    Result := TTOMLFloat.CreateText(Lex, F);
    Exit;
  end;

  { 0x / 0o / 0b }
  if (Length(Body) >= 2) and (Byte(Body[0]) = Ord('0')) and
     ((Byte(Body[1]) = Ord('x')) or (Byte(Body[1]) = Ord('o')) or
      (Byte(Body[1]) = Ord('b'))) then
  begin
    if HasSign then
      FailAt(Start, 'a sign is not allowed on a hex, octal or binary integer');
    if Byte(Body[1]) = Ord('x') then Base := 16
    else if Byte(Body[1]) = Ord('o') then Base := 8
    else Base := 2;
    Digits := Copy(Body, 2, Length(Body) - 2);
    if not TPValidDigitRun(Digits, Base) then
      FailAt(Start, 'invalid integer ' + Lex);
    Digits := TPStripUnderscores(Digits);
    Acc := 0;
    I := 0;
    while I < Length(Digits) do
    begin
      D := TPHexVal(Byte(Digits[I]));
      if Acc > (MaxInt64Value - D) div Base then
        FailAt(Start, 'integer out of range ' + Lex);
      Acc := Acc * Base + D;
      I := I + 1;
    end;
    Result := TTOMLInteger.CreateText(Lex, Acc);
    Exit;
  end;

  { decimal: int-part [ '.' frac ] [ (e|E) [sign] exp ] }
  I := 0;
  while (I < Length(Body)) and (Byte(Body[I]) <> Ord('.')) and
        (Byte(Body[I]) <> Ord('e')) and (Byte(Body[I]) <> Ord('E')) do
    I := I + 1;
  IntPart := Copy(Body, 0, I);
  FracPart := '';
  ExpPart := '';
  if (I < Length(Body)) and (Byte(Body[I]) = Ord('.')) then
  begin
    ExpPos := I + 1;
    while (ExpPos < Length(Body)) and (Byte(Body[ExpPos]) <> Ord('e')) and
          (Byte(Body[ExpPos]) <> Ord('E')) do
      ExpPos := ExpPos + 1;
    FracPart := Copy(Body, I + 1, ExpPos - I - 1);
    if not TPValidDigitRun(FracPart, 10) then
      FailAt(Start, 'invalid float ' + Lex);
    I := ExpPos;
  end;
  if I < Length(Body) then
  begin
    { at 'e' / 'E' }
    ExpPart := Copy(Body, I + 1, Length(Body) - I - 1);
    if (Length(ExpPart) > 0) and
       ((Byte(ExpPart[0]) = Ord('+')) or (Byte(ExpPart[0]) = Ord('-'))) then
      Digits := Copy(ExpPart, 1, Length(ExpPart) - 1)
    else
      Digits := ExpPart;
    if not TPValidDigitRun(Digits, 10) then
      FailAt(Start, 'invalid float ' + Lex);
    if ExpPart = '' then
      FailAt(Start, 'invalid float ' + Lex);
  end;
  if not TPValidDigitRun(IntPart, 10) then
    FailAt(Start, 'invalid number ' + Lex);
  if (Length(IntPart) > 1) and (Byte(IntPart[0]) = Ord('0')) then
    FailAt(Start, 'leading zero in number ' + Lex);
  { A stray '+' or letter anywhere is caught by the digit-run checks. }

  if Length(IntPart) = Length(Body) then
  begin
    { integer: accumulate negatively so Int64's minimum fits }
    Digits := TPStripUnderscores(IntPart);
    Acc := 0;
    I := 0;
    while I < Length(Digits) do
    begin
      D := Byte(Digits[I]) - Ord('0');
      if Acc < (-MaxInt64Value - 1 + D) div 10 then
        FailAt(Start, 'integer out of range ' + Lex);
      Acc := Acc * 10 - D;
      I := I + 1;
    end;
    if not Neg then
    begin
      if Acc = -MaxInt64Value - 1 then
        FailAt(Start, 'integer out of range ' + Lex);
      Acc := -Acc;
    end;
    Result := TTOMLInteger.CreateText(Lex, Acc);
    Exit;
  end;

  F := StrToDouble(TPStripUnderscores(Body));
  if Neg then
    F := -F;
  Result := TTOMLFloat.CreateText(Lex, F);
end;

{ Exactly ACount digits; returns their value. }
function TTOMLParser.ReadDigits(ACount: Int; const AWhat: string): Int;
var
  K: Int;
begin
  Result := 0;
  K := 0;
  while K < ACount do
  begin
    if not TPIsDigit(Peek()) then
      Fail('invalid ' + AWhat);
    Result := Result * 10 + (Peek() - Ord('0'));
    FPos := FPos + 1;
    K := K + 1;
  end;
end;

{ HH:MM:SS[.fraction] }
procedure TTOMLParser.ParseTimePart;
var
  H, M, S, StartPos: Int;
begin
  StartPos := FPos;
  H := ReadDigits(2, 'time');
  if Peek() <> Ord(':') then Fail('invalid time');
  FPos := FPos + 1;
  M := ReadDigits(2, 'time');
  if Peek() <> Ord(':') then Fail('invalid time (seconds are required)');
  FPos := FPos + 1;
  S := ReadDigits(2, 'time');
  if (H > 23) or (M > 59) or (S > 60) then
    FailAt(StartPos, 'time out of range');
  if Peek() = Ord('.') then
  begin
    FPos := FPos + 1;
    if not TPIsDigit(Peek()) then
      Fail('invalid fractional seconds');
    while TPIsDigit(Peek()) do
      FPos := FPos + 1;
  end;
end;

function TTOMLParser.ParseDateTime: TTOMLData;
var
  Start, Y, Mo, D, OH, OM: Int;
  Kind: TTOMLType;
begin
  Start := FPos;
  if PeekAt(2) = Ord(':') then
  begin
    ParseTimePart();
    Result := TTOMLDateTime.Create(ttLocalTime,
      Copy(FText, Start, FPos - Start));
    Exit;
  end;
  Y := ReadDigits(4, 'date');
  if Peek() <> Ord('-') then Fail('invalid date');
  FPos := FPos + 1;
  Mo := ReadDigits(2, 'date');
  if Peek() <> Ord('-') then Fail('invalid date');
  FPos := FPos + 1;
  D := ReadDigits(2, 'date');
  if (Mo < 1) or (Mo > 12) or (D < 1) or (D > TPDaysInMonth(Y, Mo)) then
    FailAt(Start, 'date out of range');
  Kind := ttLocalDate;
  if ((Peek() = Ord('T')) or (Peek() = Ord('t')) or (Peek() = 32)) and
     IsDigitAt(1) then
  begin
    FPos := FPos + 1;
    ParseTimePart();
    Kind := ttLocalDateTime;
    if (Peek() = Ord('Z')) or (Peek() = Ord('z')) then
    begin
      FPos := FPos + 1;
      Kind := ttOffsetDateTime;
    end
    else if (Peek() = Ord('+')) or (Peek() = Ord('-')) then
    begin
      FPos := FPos + 1;
      OH := ReadDigits(2, 'time offset');
      if Peek() <> Ord(':') then Fail('invalid time offset');
      FPos := FPos + 1;
      OM := ReadDigits(2, 'time offset');
      if (OH > 23) or (OM > 59) then
        FailAt(Start, 'time offset out of range');
      Kind := ttOffsetDateTime;
    end;
  end;
  Result := TTOMLDateTime.Create(Kind, Copy(FText, Start, FPos - Start));
end;

end.
