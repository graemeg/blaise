{
  Blaise stdlib - JSON parser
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - JSON parsing engine.

  TJSONParser is a recursive-descent parser that turns JSON text into the
  Json.Types tree.  Json.Reader is the thin GetJSON facade over it.

  Conformant to RFC 8259 for the value grammar: objects, arrays, strings (with
  the escapes \" \\ \/ \b \f \n \r \t and \uXXXX, including surrogate pairs),
  numbers (int/float discriminated by '.' / 'e'), and the true/false/null
  literals.  Malformed input raises EJSONParseError with the byte offset.

  Strings are UTF-8; \uXXXX escapes are decoded and re-encoded as UTF-8.
}

unit Json.Parser;

interface

uses
  SysUtils, StrUtils, Json.Types;

type
  EJSONParseError = class(Exception)
  end;

  TJSONParser = class
  private
    FText: string;
    FPos:  Int;
    FLen:  Int;
    procedure Fail(const AMsg: string);
    procedure SkipWhitespace;
    function  Peek: Int;                  { current byte, or -1 at end }
    function  ParseValue: TJSONData;
    function  ParseObject: TJSONObject;
    function  ParseArray: TJSONArray;
    function  ParseStringRaw: string;         { consumes a "..." token }
    function  ParseHex4: Int;             { reads 4 hex digits after \u }
    function  ParseNumber: TJSONData;
    function  ParseLiteral: TJSONData;        { true / false / null }
  public
    constructor Create(const AText: string);
    { Parse the whole document; raises EJSONParseError on malformed input. }
    function Parse: TJSONData;
  end;

implementation

constructor TJSONParser.Create(const AText: string);
begin
  FText := AText;
  FPos  := 0;
  FLen  := Length(AText);
end;

procedure TJSONParser.Fail(const AMsg: string);
begin
  raise EJSONParseError.Create(AMsg + ' at offset ' + IntToStr(FPos));
end;

function TJSONParser.Peek: Int;
begin
  if FPos < FLen then
    Result := Byte(FText[FPos])
  else
    Result := -1;
end;

procedure TJSONParser.SkipWhitespace;
var
  C: Int;
begin
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if (C = 32) or (C = 9) or (C = 10) or (C = 13) then
      FPos := FPos + 1
    else
      Exit;
  end;
end;

function TJSONParser.Parse: TJSONData;
begin
  SkipWhitespace();
  Result := ParseValue();
  SkipWhitespace();
  if FPos < FLen then
    Fail('trailing content after JSON value');
end;

function TJSONParser.ParseValue: TJSONData;
var
  C: Int;
begin
  SkipWhitespace();
  C := Peek();
  if C = Ord('{') then
    Result := ParseObject()
  else if C = Ord('[') then
    Result := ParseArray()
  else if C = Ord('"') then
    Result := TJSONString.Create(ParseStringRaw())
  else if (C = Ord('-')) or ((C >= Ord('0')) and (C <= Ord('9'))) then
    Result := ParseNumber()
  else if (C = Ord('t')) or (C = Ord('f')) or (C = Ord('n')) then
    Result := ParseLiteral()
  else
  begin
    Result := nil;
    Fail('unexpected character');
  end;
end;

function TJSONParser.ParseObject: TJSONObject;
var
  Obj: TJSONObject;
  Key: string;
begin
  Obj := TJSONObject.Create();
  FPos := FPos + 1;          { consume '{' }
  SkipWhitespace();
  if Peek() = Ord('}') then
  begin
    FPos := FPos + 1;
    Result := Obj;
    Exit;
  end;
  while True do
  begin
    SkipWhitespace();
    if Peek() <> Ord('"') then
      Fail('expected string key');
    Key := ParseStringRaw();
    SkipWhitespace();
    if Peek() <> Ord(':') then
      Fail('expected '':'' after key');
    FPos := FPos + 1;        { consume ':' }
    Obj.Add(Key, ParseValue());
    SkipWhitespace();
    if Peek() = Ord(',') then
    begin
      FPos := FPos + 1;
      Continue;
    end;
    if Peek() = Ord('}') then
    begin
      FPos := FPos + 1;
      Break;
    end;
    Fail('expected '','' or ''}'' in object');
  end;
  Result := Obj;
end;

function TJSONParser.ParseArray: TJSONArray;
var
  Arr: TJSONArray;
begin
  Arr := TJSONArray.Create();
  FPos := FPos + 1;          { consume '[' }
  SkipWhitespace();
  if Peek() = Ord(']') then
  begin
    FPos := FPos + 1;
    Result := Arr;
    Exit;
  end;
  while True do
  begin
    Arr.Add(ParseValue());
    SkipWhitespace();
    if Peek() = Ord(',') then
    begin
      FPos := FPos + 1;
      Continue;
    end;
    if Peek() = Ord(']') then
    begin
      FPos := FPos + 1;
      Break;
    end;
    Fail('expected '','' or '']'' in array');
  end;
  Result := Arr;
end;

function JPHexVal(AByte: Int): Int;
begin
  if (AByte >= Ord('0')) and (AByte <= Ord('9')) then
    Result := AByte - Ord('0')
  else if (AByte >= Ord('a')) and (AByte <= Ord('f')) then
    Result := AByte - Ord('a') + 10
  else if (AByte >= Ord('A')) and (AByte <= Ord('F')) then
    Result := AByte - Ord('A') + 10
  else
    Result := -1;
end;

{ Append codepoint ACP to ASB as UTF-8 bytes. }
procedure JPAppendUTF8(ASB: TStringBuilder; ACP: Int);
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

function TJSONParser.ParseHex4: Int;
var
  K, D, V: Int;
begin
  V := 0;
  K := 0;
  while K < 4 do
  begin
    if FPos >= FLen then
      Fail('truncated \u escape');
    D := JPHexVal(Byte(FText[FPos]));
    if D < 0 then
      Fail('bad hex digit in \u escape');
    V := V * 16 + D;
    FPos := FPos + 1;
    K := K + 1;
  end;
  Result := V;
end;

function TJSONParser.ParseStringRaw: string;
var
  SB:  TStringBuilder;
  C:   Int;
  Esc: Int;
  Hi:  Int;
  Lo:  Int;
begin
  SB := TStringBuilder.Create();
  FPos := FPos + 1;          { consume opening '"' }
  while True do
  begin
    if FPos >= FLen then
      Fail('unterminated string');
    C := Byte(FText[FPos]);
    FPos := FPos + 1;
    if C = Ord('"') then
      Break
    else if C = Ord('\') then
    begin
      if FPos >= FLen then
        Fail('unterminated escape');
      Esc := Byte(FText[FPos]);
      FPos := FPos + 1;
      if Esc = Ord('"') then SB.AppendByte(Ord('"'))
      else if Esc = Ord('\') then SB.AppendByte(Ord('\'))
      else if Esc = Ord('/') then SB.AppendByte(Ord('/'))
      else if Esc = Ord('b') then SB.AppendByte(8)
      else if Esc = Ord('f') then SB.AppendByte(12)
      else if Esc = Ord('n') then SB.AppendByte(10)
      else if Esc = Ord('r') then SB.AppendByte(13)
      else if Esc = Ord('t') then SB.AppendByte(9)
      else if Esc = Ord('u') then
      begin
        Hi := ParseHex4();
        if (Hi >= $D800) and (Hi <= $DBFF) then
        begin
          { high surrogate — expect a following \uLOW }
          if (FPos + 1 < FLen) and (Byte(FText[FPos]) = Ord('\'))
             and (Byte(FText[FPos + 1]) = Ord('u')) then
          begin
            FPos := FPos + 2;
            Lo := ParseHex4();
            JPAppendUTF8(SB, $10000 + (Hi - $D800) * $400 + (Lo - $DC00));
          end
          else
            JPAppendUTF8(SB, Hi);
        end
        else
          JPAppendUTF8(SB, Hi);
      end
      else
        Fail('bad escape');
    end
    else
      SB.AppendByte(C);
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TJSONParser.ParseNumber: TJSONData;
var
  Start: Int;
  IsInt: Boolean;
  C:     Int;
  Lex:   string;
begin
  Start := FPos;
  IsInt := True;
  if Peek() = Ord('-') then
    FPos := FPos + 1;
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if (C >= Ord('0')) and (C <= Ord('9')) then
      FPos := FPos + 1
    else if (C = Ord('.')) or (C = Ord('e')) or (C = Ord('E'))
            or (C = Ord('+')) or (C = Ord('-')) then
    begin
      if (C = Ord('.')) or (C = Ord('e')) or (C = Ord('E')) then
        IsInt := False;
      FPos := FPos + 1;
    end
    else
      Break;
  end;
  Lex := Copy(FText, Start, FPos - Start);
  Result := TJSONNumber.CreateText(Lex, IsInt);
end;

function TJSONParser.ParseLiteral: TJSONData;
begin
  if (FPos + 4 <= FLen) and (Copy(FText, FPos, 4) = 'true') then
  begin
    FPos := FPos + 4;
    Result := TJSONBoolean.Create(True);
  end
  else if (FPos + 5 <= FLen) and (Copy(FText, FPos, 5) = 'false') then
  begin
    FPos := FPos + 5;
    Result := TJSONBoolean.Create(False);
  end
  else if (FPos + 4 <= FLen) and (Copy(FText, FPos, 4) = 'null') then
  begin
    FPos := FPos + 4;
    Result := TJSONNull.Create();
  end
  else
  begin
    Result := nil;
    Fail('invalid literal');
  end;
end;

end.
