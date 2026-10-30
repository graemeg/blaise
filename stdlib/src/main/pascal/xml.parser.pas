{
  Blaise stdlib - XML parser
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - XML parsing engine.

  TXMLParser is a recursive-descent parser that turns XML text into the
  Xml.Types tree.  Xml.Reader is the thin GetXML facade over it.

  Supported: elements, attributes (single- or double-quoted), text, CDATA
  sections, comments, processing instructions, the XML declaration
  (version/encoding captured on the document), the five predefined entities
  (&amp; &lt; &gt; &quot; &apos;) and numeric character references
  (&#nn; / &#xHH;, decoded to UTF-8).  A DOCTYPE declaration is skipped,
  including its internal subset; custom entities it declares are NOT
  processed.  Malformed input raises EXMLParseError with the byte offset.

  Deliberately out of scope (documented, not accidental): DTD validation,
  external entities (a security hazard), and namespace resolution - prefixed
  names like 'svg:rect' are kept verbatim as element/attribute names.

  Whitespace-only text nodes between elements are dropped by default so that
  pretty-printed input parses to a clean tree; set PreserveWhitespace to True
  to keep them.  Text nodes with any non-whitespace content are always kept
  verbatim.  Strings are treated as UTF-8 throughout.

  Doc-level comments and processing instructions outside the root element are
  skipped (the document model keeps only the root element and declaration).
}

unit Xml.Parser;

interface

uses
  SysUtils, StrUtils, Xml.Types;

type
  EXMLParseError = class(Exception)
  end;

  TXMLParser = class
  private
    FText: string;
    FPos: Int;
    FLen: Int;
    FPreserveWhitespace: Boolean;
    procedure Fail(const AMsg: string);
    function Peek: Int;                   { current byte, or -1 at end }
    function Match(const S: string): Boolean; { does S start at FPos? }
    procedure Expect(const S: string);        { Match + consume, or Fail }
    procedure SkipWhitespace;
    procedure SkipMisc;                       { ws / comments / PIs / DOCTYPE }
    procedure SkipDoctype;
    function ParseName: string;
    function ParseAttrValue: string;
    function DecodeEntity: string;            { consumes '&...;' }
    function ParseTextRun: string;            { text up to the next '<' }
    function ParseComment: string;            { after '<!--', up to '-->' }
    function ParseCData: string;              { after '<![CDATA[' }
    procedure ParsePI(var ATarget, AContent: string);  { after '<?' }
    procedure ParseDeclaration(ADoc: TXMLDocument);    { optional <?xml ...?> }
    function ParseElement: TXMLElement;
    procedure ParseContent(AElem: TXMLElement);
  public
    constructor Create(const AText: string);
    { Parse the whole document; raises EXMLParseError on malformed input. }
    function Parse: TXMLDocument;
    { Keep whitespace-only text nodes (default False: they are dropped). }
    property PreserveWhitespace: Boolean
      read FPreserveWhitespace write FPreserveWhitespace;
  end;

implementation

{ ------------------------------------------------------------------ }
{ helpers                                                             }
{ ------------------------------------------------------------------ }

function XPIsWhitespace(C: Int): Boolean;
begin
  Result := (C = 32) or (C = 9) or (C = 10) or (C = 13);
end;

function XPIsNameStart(C: Int): Boolean;
begin
  Result := ((C >= Ord('a')) and (C <= Ord('z')))
    or ((C >= Ord('A')) and (C <= Ord('Z')))
    or (C = Ord('_')) or (C = Ord(':'))
    or (C >= 128);   { multi-byte UTF-8 name characters pass through }
end;

function XPIsNameChar(C: Int): Boolean;
begin
  Result := XPIsNameStart(C)
    or ((C >= Ord('0')) and (C <= Ord('9')))
    or (C = Ord('-')) or (C = Ord('.'));
end;

function XPIsAllWhitespace(const S: string): Boolean;
var
  I: Int;
begin
  Result := True;
  I := 0;
  while I < Length(S) do
  begin
    if not XPIsWhitespace(Byte(S[I])) then
    begin
      Result := False;
      Exit;
    end;
    I := I + 1;
  end;
end;

function XPHexVal(AByte: Int): Int;
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

{ ------------------------------------------------------------------ }
{ TXMLParser                                                         }
{ ------------------------------------------------------------------ }

constructor TXMLParser.Create(const AText: string);
begin
  FText := AText;
  FPos := 0;
  FLen := Length(AText);
  FPreserveWhitespace := False;
end;

procedure TXMLParser.Fail(const AMsg: string);
begin
  raise EXMLParseError.Create(AMsg + ' at offset ' + IntToStr(FPos));
end;

function TXMLParser.Peek: Int;
begin
  if FPos < FLen then
    Result := Byte(FText[FPos])
  else
    Result := -1;
end;

function TXMLParser.Match(const S: string): Boolean;
begin
  Result := (FPos + Length(S) <= FLen)
    and (Copy(FText, FPos, Length(S)) = S);
end;

procedure TXMLParser.Expect(const S: string);
begin
  if Match(S) then
    FPos := FPos + Length(S)
  else
    Fail('expected ''' + S + '''');
end;

procedure TXMLParser.SkipWhitespace;
begin
  while (FPos < FLen) and XPIsWhitespace(Byte(FText[FPos])) do
    FPos := FPos + 1;
end;

procedure TXMLParser.SkipDoctype;
var
  C, Depth: Int;
begin
  FPos := FPos + 9;          { consume '<!DOCTYPE' }
  Depth := 0;
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    FPos := FPos + 1;
    if C = Ord('[') then
      Depth := Depth + 1
    else if C = Ord(']') then
      Depth := Depth - 1
    else if (C = Ord('>')) and (Depth <= 0) then
      Exit;
  end;
  Fail('unterminated DOCTYPE');
end;

procedure TXMLParser.SkipMisc;
var
  T, C: string;
begin
  while True do
  begin
    SkipWhitespace();
    if Match('<!--') then
    begin
      FPos := FPos + 4;
      T := ParseComment();       { discarded at document level }
    end
    else if Match('<!DOCTYPE') then
      SkipDoctype()
    else if Match('<?') then
    begin
      FPos := FPos + 2;
      ParsePI(T, C);             { discarded at document level }
    end
    else
      Exit;
  end;
end;

function TXMLParser.ParseName: string;
var
  Start: Int;
begin
  Result := '';
  if not XPIsNameStart(Peek()) then
    Fail('expected a name');
  Start := FPos;
  while (FPos < FLen) and XPIsNameChar(Byte(FText[FPos])) do
    FPos := FPos + 1;
  Result := Copy(FText, Start, FPos - Start);
end;

function TXMLParser.DecodeEntity: string;
var
  C, CP, D, Start: Int;
  IsHex, GotDigit: Boolean;
  Name: string;
begin
  Result := '';
  FPos := FPos + 1;            { consume '&' }
  if Peek() = Ord('#') then
  begin
    FPos := FPos + 1;
    IsHex := False;
    if (Peek() = Ord('x')) or (Peek() = Ord('X')) then
    begin
      IsHex := True;
      FPos := FPos + 1;
    end;
    CP := 0;
    GotDigit := False;
    while FPos < FLen do
    begin
      C := Byte(FText[FPos]);
      if IsHex then
      begin
        D := XPHexVal(C);
        if D < 0 then
          Break;
        CP := CP * 16 + D;
      end
      else
      begin
        if (C < Ord('0')) or (C > Ord('9')) then
          Break;
        CP := CP * 10 + (C - Ord('0'));
      end;
      GotDigit := True;
      FPos := FPos + 1;
      if CP > $10FFFF then
        Fail('character reference out of range');
    end;
    if not GotDigit then
      Fail('malformed character reference');
    if Peek() <> Ord(';') then
      Fail('unterminated character reference');
    FPos := FPos + 1;
    Result := CodePointToString(CP);
  end
  else
  begin
    Start := FPos;
    while (FPos < FLen) and (Byte(FText[FPos]) <> Ord(';'))
      and (FPos - Start < 10) do
      FPos := FPos + 1;
    if Peek() <> Ord(';') then
      Fail('unterminated entity reference');
    Name := Copy(FText, Start, FPos - Start);
    FPos := FPos + 1;
    if Name = 'amp' then Result := '&'
    else if Name = 'lt' then Result := '<'
    else if Name = 'gt' then Result := '>'
    else if Name = 'quot' then Result := '"'
    else if Name = 'apos' then Result := ''''
    else
      Fail('unknown entity &' + Name + ';');
  end;
end;

function TXMLParser.ParseAttrValue: string;
var
  Q, C: Int;
  SB: TStringBuilder;
begin
  Result := '';
  Q := Peek();
  if (Q <> 34) and (Q <> 39) then   { " or ' }
    Fail('expected a quoted attribute value');
  FPos := FPos + 1;
  SB := TStringBuilder.Create();
  while True do
  begin
    if FPos >= FLen then
      Fail('unterminated attribute value');
    C := Byte(FText[FPos]);
    if C = Q then
    begin
      FPos := FPos + 1;
      Break;
    end
    else if C = Ord('&') then
      SB.Append(DecodeEntity())
    else if C = Ord('<') then
      Fail('''<'' is not allowed in an attribute value')
    else
    begin
      SB.AppendByte(C);
      FPos := FPos + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TXMLParser.ParseTextRun: string;
var
  C: Int;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  while FPos < FLen do
  begin
    C := Byte(FText[FPos]);
    if C = Ord('<') then
      Break
    else if C = Ord('&') then
      SB.Append(DecodeEntity())
    else
    begin
      SB.AppendByte(C);
      FPos := FPos + 1;
    end;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function TXMLParser.ParseComment: string;
var
  Start: Int;
begin
  Result := '';
  Start := FPos;
  while (FPos + 3 <= FLen) and (not Match('-->')) do
    FPos := FPos + 1;
  if not Match('-->') then
    Fail('unterminated comment');
  Result := Copy(FText, Start, FPos - Start);
  FPos := FPos + 3;
end;

function TXMLParser.ParseCData: string;
var
  Start: Int;
begin
  Result := '';
  Start := FPos;
  while (FPos + 3 <= FLen) and (not Match(']]>')) do
    FPos := FPos + 1;
  if not Match(']]>') then
    Fail('unterminated CDATA section');
  Result := Copy(FText, Start, FPos - Start);
  FPos := FPos + 3;
end;

procedure TXMLParser.ParsePI(var ATarget, AContent: string);
var
  Start: Int;
begin
  ATarget := ParseName();
  SkipWhitespace();
  Start := FPos;
  while (FPos + 2 <= FLen) and (not Match('?>')) do
    FPos := FPos + 1;
  if not Match('?>') then
    Fail('unterminated processing instruction');
  AContent := Copy(FText, Start, FPos - Start);
  FPos := FPos + 2;
end;

procedure TXMLParser.ParseDeclaration(ADoc: TXMLDocument);
var
  AfterXml: Int;
  AttrName, AttrVal: string;
begin
  if not Match('<?xml') then
    Exit;
  if FPos + 5 < FLen then
    AfterXml := Byte(FText[FPos + 5])
  else
    AfterXml := -1;
  { only a real declaration: '<?xml' followed by whitespace or '?' }
  if (not XPIsWhitespace(AfterXml)) and (AfterXml <> Ord('?')) then
    Exit;
  FPos := FPos + 5;
  while True do
  begin
    SkipWhitespace();
    if Match('?>') then
    begin
      FPos := FPos + 2;
      Exit;
    end;
    if FPos >= FLen then
      Fail('unterminated XML declaration');
    AttrName := ParseName();
    SkipWhitespace();
    Expect('=');
    SkipWhitespace();
    AttrVal := ParseAttrValue();
    if AttrName = 'version' then
      ADoc.Version := AttrVal
    else if AttrName = 'encoding' then
      ADoc.Encoding := AttrVal;
    { 'standalone' and anything else: accepted and ignored }
  end;
end;

function TXMLParser.ParseElement: TXMLElement;
var
  Elem: TXMLElement;
  AttrName, AttrVal: string;
  C: Int;
begin
  Result := nil;
  Expect('<');
  Elem := TXMLElement.Create(ParseName());
  while True do
  begin
    SkipWhitespace();
    C := Peek();
    if C = Ord('>') then
    begin
      FPos := FPos + 1;
      ParseContent(Elem);
      Break;
    end
    else if Match('/>') then
    begin
      FPos := FPos + 2;
      Break;
    end
    else if C < 0 then
      Fail('unterminated start tag <' + Elem.Name + '>')
    else
    begin
      AttrName := ParseName();
      SkipWhitespace();
      Expect('=');
      SkipWhitespace();
      AttrVal := ParseAttrValue();
      if Elem.HasAttribute(AttrName) then
        Fail('duplicate attribute "' + AttrName + '"');
      Elem.SetAttribute(AttrName, AttrVal);
    end;
  end;
  Result := Elem;
end;

procedure TXMLParser.ParseContent(AElem: TXMLElement);
var
  CloseName, Txt, PITarget, PIContent: string;
begin
  while True do
  begin
    if FPos >= FLen then
      Fail('unterminated element <' + AElem.Name + '>');
    if Match('</') then
    begin
      FPos := FPos + 2;
      CloseName := ParseName();
      SkipWhitespace();
      Expect('>');
      if CloseName <> AElem.Name then
        Fail('mismatched closing tag </' + CloseName
          + '> (expected </' + AElem.Name + '>)');
      Exit;
    end
    else if Match('<!--') then
    begin
      FPos := FPos + 4;
      AElem.AddComment(ParseComment());
    end
    else if Match('<![CDATA[') then
    begin
      FPos := FPos + 9;
      AElem.AddCData(ParseCData());
    end
    else if Match('<?') then
    begin
      FPos := FPos + 2;
      ParsePI(PITarget, PIContent);
      AElem.Add(TXMLProcessingInstruction.Create(PITarget, PIContent));
    end
    else if Match('<!') then
      Fail('unexpected markup declaration inside an element')
    else if Peek() = Ord('<') then
      AElem.Add(Self.ParseElement())
    else
    begin
      Txt := ParseTextRun();
      if FPreserveWhitespace or (not XPIsAllWhitespace(Txt)) then
        AElem.AddText(Txt);
    end;
  end;
end;

function TXMLParser.Parse: TXMLDocument;
var
  Doc: TXMLDocument;
begin
  FPos := 0;
  { skip a UTF-8 byte-order mark }
  if (FLen >= 3) and (Byte(FText[0]) = $EF) and (Byte(FText[1]) = $BB)
    and (Byte(FText[2]) = $BF) then
    FPos := 3;
  Doc := TXMLDocument.Create();
  ParseDeclaration(Doc);
  SkipMisc();
  if Peek() <> Ord('<') then
    Fail('expected a root element');
  Doc.Root := Self.ParseElement();
  SkipMisc();
  if FPos < FLen then
    Fail('trailing content after the root element');
  Result := Doc;
end;

end.
