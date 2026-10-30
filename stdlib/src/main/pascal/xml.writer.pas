{
  Blaise stdlib - XML writer
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - streaming XML writer.

  TXMLWriter emits an XML document by announcing structure as you go: open an
  element, write attributes and content, close it.  Output is accumulated in a
  TStringBuilder, so building even a large document is O(n).  The design
  follows .NET's XmlWriter and Java's StAX XMLStreamWriter.

  Typical usage:

      W := TXMLWriter.Create();
      W.WriteDeclaration();                 // <?xml version="1.0" ...?>
      W.BeginElement('book');
      W.WriteAttribute('id', 'b1');         // attributes before any content
      W.WriteElement('title', 'Dune');      // one-shot <title>Dune</title>
      W.BeginElement('tags');
        W.WriteElement('tag', 'scifi');
      W.EndElement();
      W.EndElement();
      S := W.ToString();

  Rules the writer enforces (EXMLWriterError otherwise):

    * WriteAttribute is only legal while the start tag is still open, i.e.
      between BeginElement and the first piece of content.
    * Text (WriteText / WriteCData) must be inside an element.
    * EndElement must match a BeginElement.

  An element closed without any content is emitted self-closing (<br/>).
  Text and attribute values are escaped automatically; WriteCData splits any
  embedded ']]>' across two CDATA sections so the output is always well-formed.
  Comments and PI content are emitted verbatim - the caller must not embed
  '-->' / '?>' in them.

  Set Pretty (and Indent) before writing for human-readable output; elements
  containing only text stay on one line (<title>Dune</title>).  The default is
  compact.  WriteDeclaration always ends with a newline in both modes.

  This unit is self-contained: it does not depend on the XML document/DOM
  types.  Xml.Types layers the tree model on top of this writer.
}

unit Xml.Writer;

interface

uses
  SysUtils, StrUtils;

type
  EXMLWriterError = class(Exception)
  end;

  TXMLWriter = class
  private
    FSB: TStringBuilder;
    FPretty: Boolean;
    FIndent: Int;                     { spaces per level when pretty }
    { Parallel per-depth stacks for the open elements. }
    FNames: array of string;
    FHasContent: array of Boolean;        { any content written inside }
    FHasElemContent: array of Boolean;    { element/comment/PI content inside }
    FTagOpen: Boolean;                    { '<name' emitted, '>' still pending }
    procedure NewlineIndent(ALevel: Int);
    procedure CloseOpenTag;
    procedure MarkContent(AElementContent: Boolean);
    procedure RequireElement(const AWhat: string);
  public
    constructor Create;
    destructor Destroy; override;

    { <?xml version="1.0" encoding="UTF-8"?> followed by a newline. }
    procedure WriteDeclaration; overload;
    procedure WriteDeclaration(const AVersion, AEncoding: string); overload;

    { ---- structure ---- }
    procedure BeginElement(const AName: string);
    procedure EndElement;
    { Attributes are only legal while the start tag is open. }
    procedure WriteAttribute(const AName, AValue: string);

    { ---- content ---- }
    procedure WriteText(const AText: string);           { escaped }
    { One-shot <name>text</name>; empty text yields <name/>. }
    procedure WriteElement(const AName, AText: string);
    procedure WriteCData(const AText: string);
    procedure WriteComment(const AText: string);
    procedure WriteProcessingInstruction(const ATarget, AContent: string);
    { Emit a verbatim, already-formatted XML fragment as content. }
    procedure WriteRaw(const AFragment: string);

    { The accumulated document so far. }
    function ToString: string; override;
    { Discard all output and reset to an empty document. }
    procedure Reset;

    property Pretty: Boolean read FPretty write FPretty;
    property Indent: Int read FIndent write FIndent;
  end;

{ Escape text content: & < > }
function XMLEscapeText(const S: string): string;
{ Escape an attribute value (emitted in double quotes): & < > " and
  TAB/LF/CR as character references so they survive a round trip. }
function XMLEscapeAttr(const S: string): string;

implementation

function XMLEscapeText(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Int;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if B = 38 then SB.Append('&amp;')        { & }
    else if B = 60 then SB.Append('&lt;')    { < }
    else if B = 62 then SB.Append('&gt;')    { > }
    else
      SB.AppendByte(B);
    I := I + 1;
  end;
  Result := SB.ToString();
  SB.Free();
end;

function XMLEscapeAttr(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Int;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if B = 38 then SB.Append('&amp;')        { & }
    else if B = 60 then SB.Append('&lt;')    { < }
    else if B = 62 then SB.Append('&gt;')    { > }
    else if B = 34 then SB.Append('&quot;')  { " }
    else if B = 9 then SB.Append('&#9;')
    else if B = 10 then SB.Append('&#10;')
    else if B = 13 then SB.Append('&#13;')
    else
      SB.AppendByte(B);
    I := I + 1;
  end;
  Result := SB.ToString();
  SB.Free();
end;

constructor TXMLWriter.Create;
begin
  FSB := TStringBuilder.Create();
  FPretty := False;
  FIndent := 2;
  FTagOpen := False;
end;

destructor TXMLWriter.Destroy;
begin
  FSB.Free();
  inherited Destroy();
end;

procedure TXMLWriter.NewlineIndent(ALevel: Int);
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

procedure TXMLWriter.CloseOpenTag;
begin
  if FTagOpen then
  begin
    FSB.Append('>');
    FTagOpen := False;
  end;
end;

{ Record that the innermost open element received content.  Element-like
  content (child elements, comments, PIs) also forces the closing tag onto its
  own line in pretty mode; plain text keeps the element on one line. }
procedure TXMLWriter.MarkContent(AElementContent: Boolean);
var
  Top: Int;
begin
  Top := Length(FNames) - 1;
  if Top < 0 then
    Exit;
  FHasContent[Top] := True;
  if AElementContent then
    FHasElemContent[Top] := True;
end;

procedure TXMLWriter.RequireElement(const AWhat: string);
begin
  if Length(FNames) = 0 then
    raise EXMLWriterError.Create(AWhat + ' outside an element');
end;

procedure TXMLWriter.WriteDeclaration;
begin
  WriteDeclaration('1.0', 'UTF-8');
end;

procedure TXMLWriter.WriteDeclaration(const AVersion, AEncoding: string);
begin
  FSB.Append('<?xml version="');
  FSB.Append(AVersion);
  FSB.Append('" encoding="');
  FSB.Append(AEncoding);
  FSB.Append('"?>');
  FSB.AppendByte(10);
end;

procedure TXMLWriter.BeginElement(const AName: string);
begin
  CloseOpenTag();
  if Length(FNames) > 0 then
    NewlineIndent(Length(FNames));
  MarkContent(True);
  SetLength(FNames, Length(FNames) + 1);
  SetLength(FHasContent, Length(FHasContent) + 1);
  SetLength(FHasElemContent, Length(FHasElemContent) + 1);
  FNames[Length(FNames) - 1] := AName;
  FHasContent[Length(FNames) - 1] := False;
  FHasElemContent[Length(FNames) - 1] := False;
  FSB.Append('<');
  FSB.Append(AName);
  FTagOpen := True;
end;

procedure TXMLWriter.EndElement;
var
  Top: Int;
  Nm: string;
  HadElem: Boolean;
begin
  Top := Length(FNames) - 1;
  if Top < 0 then
    raise EXMLWriterError.Create('EndElement without matching BeginElement');
  Nm := FNames[Top];
  HadElem := FHasElemContent[Top];
  SetLength(FNames, Top);
  SetLength(FHasContent, Top);
  SetLength(FHasElemContent, Top);
  if FTagOpen then
  begin
    { no content was written - emit a self-closing tag }
    FSB.Append('/>');
    FTagOpen := False;
  end
  else
  begin
    if HadElem then
      NewlineIndent(Length(FNames));
    FSB.Append('</');
    FSB.Append(Nm);
    FSB.Append('>');
  end;
end;

procedure TXMLWriter.WriteAttribute(const AName, AValue: string);
begin
  if not FTagOpen then
    raise EXMLWriterError.Create(
      'WriteAttribute is only legal directly after BeginElement');
  FSB.Append(' ');
  FSB.Append(AName);
  FSB.Append('="');
  FSB.Append(XMLEscapeAttr(AValue));
  FSB.Append('"');
end;

procedure TXMLWriter.WriteText(const AText: string);
begin
  RequireElement('WriteText');
  CloseOpenTag();
  MarkContent(False);
  FSB.Append(XMLEscapeText(AText));
end;

procedure TXMLWriter.WriteElement(const AName, AText: string);
begin
  BeginElement(AName);
  if AText <> '' then
    WriteText(AText);
  EndElement();
end;

procedure TXMLWriter.WriteCData(const AText: string);
var
  Rest: string;
  P: Int;
begin
  RequireElement('WriteCData');
  CloseOpenTag();
  MarkContent(False);
  { ']]>' cannot appear inside a CDATA section - split it across two so the
    output stays well-formed: break between ']]' and '>'. }
  Rest := AText;
  P := Pos(']]>', Rest);
  while P >= 0 do
  begin
    FSB.Append('<![CDATA[');
    FSB.Append(Copy(Rest, 0, P + 2));
    FSB.Append(']]>');
    Rest := Copy(Rest, P + 2, Length(Rest) - (P + 2));
    P := Pos(']]>', Rest);
  end;
  FSB.Append('<![CDATA[');
  FSB.Append(Rest);
  FSB.Append(']]>');
end;

procedure TXMLWriter.WriteComment(const AText: string);
begin
  CloseOpenTag();
  if Length(FNames) > 0 then
    NewlineIndent(Length(FNames));
  MarkContent(True);
  FSB.Append('<!--');
  FSB.Append(AText);
  FSB.Append('-->');
end;

procedure TXMLWriter.WriteProcessingInstruction(const ATarget, AContent: string);
begin
  CloseOpenTag();
  if Length(FNames) > 0 then
    NewlineIndent(Length(FNames));
  MarkContent(True);
  FSB.Append('<?');
  FSB.Append(ATarget);
  if AContent <> '' then
  begin
    FSB.Append(' ');
    FSB.Append(AContent);
  end;
  FSB.Append('?>');
end;

procedure TXMLWriter.WriteRaw(const AFragment: string);
begin
  CloseOpenTag();
  MarkContent(False);
  FSB.Append(AFragment);
end;

function TXMLWriter.ToString: string;
begin
  Result := FSB.ToString();
end;

procedure TXMLWriter.Reset;
begin
  FSB.Free();
  FSB := TStringBuilder.Create();
  FTagOpen := False;
  SetLength(FNames, 0);
  SetLength(FHasContent, 0);
  SetLength(FHasElemContent, 0);
end;

end.
