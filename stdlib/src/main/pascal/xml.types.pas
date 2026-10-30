{
  Blaise stdlib - XML document model (DOM)
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - the in-memory XML document model.

  TXMLNode is the abstract base; the concrete node types are TXMLElement,
  TXMLText, TXMLCData, TXMLComment and TXMLProcessingInstruction.
  TXMLDocument wraps the root element plus the declaration (version/encoding).
  Both the reader (Xml.Parser / Xml.Reader) and code that builds a document by
  hand target this one tree, so XML round-trips through it.  The navigation
  API takes after .NET's XLinq (XElement) and Java's JDOM.

  Building a document:

      Lib := TXMLElement.Create('library');
      Book := Lib.AddElement('book');           // create + adopt + return
      Book.SetAttribute('id', 'b1');
      Book.AddElement('title', 'Dune');         // <title>Dune</title>
      WriteLn(Lib.FormatXML());                 // pretty
      WriteLn(Lib.AsXML());                     // compact

  Reading a parsed document:

      Doc := GetXML(S);                         // from Xml.Reader
      for each book: Doc.Root.Elements('book')  // TList<TXMLElement>
      Title := Book.ChildText('title');         // '' if absent
      Id := Book.Attributes['id'];              // '' if absent

  Memory model: parent-owns-child.  Containers hold STRONG references to
  their children, so under Blaise ARC, releasing the root recursively releases
  the whole tree.  Add() adopts the node: never Add the same node to two
  parents, and never Add a node you also keep a separate owning reference to
  and free yourself.  Use Extract() to move a node out of one parent before
  placing it in another.  Nodes carry no parent back-pointer, so no retain
  cycles arise.

  Elements(…) returns a freshly-created TList<TXMLElement> that the CALLER
  frees; the elements themselves remain owned by their parent.

  Serialisation is delegated to Xml.Writer (the single emit kernel): AsXML is
  compact, FormatXML is pretty.  The writer has no dependency on this unit,
  so streaming-only callers need not pull in the DOM.
}

unit Xml.Types;

interface

uses
  SysUtils, StrUtils, Generics.Collections, Xml.Writer;

type
  TXMLNodeType = (xtElement, xtText, xtCData, xtComment,
    xtProcessingInstruction);

  TXMLNode = class
  protected
    function GetNodeType: TXMLNodeType; virtual; abstract;
  public
    { Drive AWriter to emit this node and its descendants. }
    procedure WriteTo(AWriter: TXMLWriter); virtual; abstract;
    function AsXML: string;                           { compact }
    function FormatXML: string; overload;             { pretty, 2-space indent }
    function FormatXML(AIndent: Int): string; overload;
    property NodeType: TXMLNodeType read GetNodeType;
  end;

  TXMLText = class(TXMLNode)
  protected
    FValue: string;
    function GetNodeType: TXMLNodeType; override;
  public
    constructor Create(const AValue: string);
    procedure WriteTo(AWriter: TXMLWriter); override;
    property Value: string read FValue write FValue;
  end;

  TXMLCData = class(TXMLNode)
  protected
    FValue: string;
    function GetNodeType: TXMLNodeType; override;
  public
    constructor Create(const AValue: string);
    procedure WriteTo(AWriter: TXMLWriter); override;
    property Value: string read FValue write FValue;
  end;

  TXMLComment = class(TXMLNode)
  protected
    FValue: string;
    function GetNodeType: TXMLNodeType; override;
  public
    constructor Create(const AValue: string);
    procedure WriteTo(AWriter: TXMLWriter); override;
    property Value: string read FValue write FValue;
  end;

  TXMLProcessingInstruction = class(TXMLNode)
  protected
    FTarget: string;
    FContent: string;
    function GetNodeType: TXMLNodeType; override;
  public
    constructor Create(const ATarget, AContent: string);
    procedure WriteTo(AWriter: TXMLWriter); override;
    property Target: string read FTarget write FTarget;
    property Content: string read FContent write FContent;
  end;

  TXMLElement = class(TXMLNode)
  private
    FName: string;
    FAttrs: TOrderedDictionary<string, string>;   { insertion-ordered }
    FChildren: TList<TXMLNode>;                   { parent owns these (strong) }
    function GetCount: Int;
    function GetItem(AIndex: Int): TXMLNode;
    function GetText: string;
    procedure SetText(const AValue: string);
    function GetAttributeCount: Int;
  protected
    function GetNodeType: TXMLNodeType; override;
  public
    constructor Create(const AName: string);
    procedure WriteTo(AWriter: TXMLWriter); override;

    { ---- attributes ---- }
    function GetAttribute(const AName: string): string;   { '' if absent }
    procedure SetAttribute(const AName, AValue: string);  { add or replace }
    function HasAttribute(const AName: string): Boolean;
    { Remove an attribute; True if it existed. }
    function RemoveAttribute(const AName: string): Boolean;
    function AttributeName(AIndex: Int): string;
    function AttributeValue(AIndex: Int): string;
    property AttributeCount: Int read GetAttributeCount;
    property Attributes[AName: string]: string
      read GetAttribute write SetAttribute;

    { ---- children: building ---- }
    { Adopt ANode as the last child; returns its index. }
    function Add(ANode: TXMLNode): Int;
    { Create a child element, adopt it and return it (chainable). }
    function AddElement(const AName: string): TXMLElement; overload;
    { Create a child element with text content: <name>text</name>. }
    function AddElement(const AName, AText: string): TXMLElement; overload;
    procedure AddText(const AText: string);
    procedure AddCData(const AText: string);
    procedure AddComment(const AText: string);

    { ---- children: navigation ---- }
    { First child element with the given name; nil if absent. }
    function Find(const AName: string): TXMLElement;
    { Text of the first child element with the given name; '' if absent. }
    function ChildText(const AName: string): string;
    { All child elements.  Returns a NEW list the caller frees; the elements
      remain owned by this parent. }
    function Elements: TList<TXMLElement>; overload;
    { All child elements with the given name (new list, caller frees). }
    function Elements(const AName: string): TList<TXMLElement>; overload;

    { ---- children: mutation ---- }
    { Detach the child at AIndex and return it; the caller then owns it. }
    function Extract(AIndex: Int): TXMLNode;
    { Detach and discard the child at AIndex (ARC frees it). }
    procedure Delete(AIndex: Int);
    procedure Clear;

    property Name: string read FName write FName;
    property Count: Int read GetCount;
    property Items[AIndex: Int]: TXMLNode read GetItem; default;
    { Concatenated text of all descendant text/CDATA nodes (like XLinq's
      XElement.Value).  Assigning replaces all children with one text node. }
    property Text: string read GetText write SetText;
  end;

  { A document: the root element plus the XML declaration values. }
  TXMLDocument = class
  private
    FRoot: TXMLElement;      { owned (strong) }
    FVersion: string;
    FEncoding: string;
  public
    constructor Create;
    function AsXML: string;                           { declaration + root }
    function FormatXML: string; overload;
    function FormatXML(AIndent: Int): string; overload;
    { Assigning Root adopts the element. }
    property Root: TXMLElement read FRoot write FRoot;
    property Version: string read FVersion write FVersion;
    property Encoding: string read FEncoding write FEncoding;
  end;

implementation

{ ------------------------------------------------------------------ }
{ helpers                                                             }
{ ------------------------------------------------------------------ }

{ Append the concatenated text/CDATA content of AElem's subtree to ASB. }
procedure XTCollectText(AElem: TXMLElement; ASB: TStringBuilder);
var
  I: Int;
  N: TXMLNode;
begin
  I := 0;
  while I < AElem.Count do
  begin
    N := AElem.Items[I];
    if N.NodeType = xtText then
      ASB.Append(TXMLText(N).Value)
    else if N.NodeType = xtCData then
      ASB.Append(TXMLCData(N).Value)
    else if N.NodeType = xtElement then
      XTCollectText(TXMLElement(N), ASB);
    I := I + 1;
  end;
end;

{ ------------------------------------------------------------------ }
{ TXMLNode                                                           }
{ ------------------------------------------------------------------ }

function TXMLNode.AsXML: string;
var
  W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.Pretty := False;
  WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

function TXMLNode.FormatXML: string;
begin
  Result := FormatXML(2);
end;

function TXMLNode.FormatXML(AIndent: Int): string;
var
  W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.Pretty := True;
  W.Indent := AIndent;
  WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

{ ------------------------------------------------------------------ }
{ TXMLText                                                           }
{ ------------------------------------------------------------------ }

constructor TXMLText.Create(const AValue: string);
begin
  FValue := AValue;
end;

function TXMLText.GetNodeType: TXMLNodeType;
begin
  Result := xtText;
end;

procedure TXMLText.WriteTo(AWriter: TXMLWriter);
begin
  AWriter.WriteText(FValue);
end;

{ ------------------------------------------------------------------ }
{ TXMLCData                                                          }
{ ------------------------------------------------------------------ }

constructor TXMLCData.Create(const AValue: string);
begin
  FValue := AValue;
end;

function TXMLCData.GetNodeType: TXMLNodeType;
begin
  Result := xtCData;
end;

procedure TXMLCData.WriteTo(AWriter: TXMLWriter);
begin
  AWriter.WriteCData(FValue);
end;

{ ------------------------------------------------------------------ }
{ TXMLComment                                                        }
{ ------------------------------------------------------------------ }

constructor TXMLComment.Create(const AValue: string);
begin
  FValue := AValue;
end;

function TXMLComment.GetNodeType: TXMLNodeType;
begin
  Result := xtComment;
end;

procedure TXMLComment.WriteTo(AWriter: TXMLWriter);
begin
  AWriter.WriteComment(FValue);
end;

{ ------------------------------------------------------------------ }
{ TXMLProcessingInstruction                                          }
{ ------------------------------------------------------------------ }

constructor TXMLProcessingInstruction.Create(const ATarget, AContent: string);
begin
  FTarget := ATarget;
  FContent := AContent;
end;

function TXMLProcessingInstruction.GetNodeType: TXMLNodeType;
begin
  Result := xtProcessingInstruction;
end;

procedure TXMLProcessingInstruction.WriteTo(AWriter: TXMLWriter);
begin
  AWriter.WriteProcessingInstruction(FTarget, FContent);
end;

{ ------------------------------------------------------------------ }
{ TXMLElement                                                        }
{ ------------------------------------------------------------------ }

constructor TXMLElement.Create(const AName: string);
begin
  FName := AName;
  FAttrs := TOrderedDictionary<string, string>.Create();
  FChildren := TList<TXMLNode>.Create();
end;

function TXMLElement.GetNodeType: TXMLNodeType;
begin
  Result := xtElement;
end;

procedure TXMLElement.WriteTo(AWriter: TXMLWriter);
var
  I: Int;
begin
  AWriter.BeginElement(FName);
  I := 0;
  while I < FAttrs.Count do
  begin
    AWriter.WriteAttribute(FAttrs.Keys[I], FAttrs.Values[I]);
    I := I + 1;
  end;
  I := 0;
  while I < FChildren.Count do
  begin
    FChildren[I].WriteTo(AWriter);
    I := I + 1;
  end;
  AWriter.EndElement();
end;

{ ---- attributes ---- }

function TXMLElement.GetAttribute(const AName: string): string;
var
  V: string;
begin
  if FAttrs.TryGetValue(AName, V) then
    Result := V
  else
    Result := '';
end;

procedure TXMLElement.SetAttribute(const AName, AValue: string);
begin
  { TOrderedDictionary.Add upserts: replaces in place, else appends. }
  FAttrs.Add(AName, AValue);
end;

function TXMLElement.HasAttribute(const AName: string): Boolean;
begin
  Result := FAttrs.ContainsKey(AName);
end;

function TXMLElement.RemoveAttribute(const AName: string): Boolean;
begin
  Result := FAttrs.ContainsKey(AName);
  if Result then
    FAttrs.Remove(AName);
end;

function TXMLElement.GetAttributeCount: Int;
begin
  Result := FAttrs.Count;
end;

function TXMLElement.AttributeName(AIndex: Int): string;
begin
  Result := FAttrs.Keys[AIndex];
end;

function TXMLElement.AttributeValue(AIndex: Int): string;
begin
  Result := FAttrs.Values[AIndex];
end;

{ ---- children: building ---- }

function TXMLElement.Add(ANode: TXMLNode): Int;
begin
  FChildren.Add(ANode);
  Result := FChildren.Count - 1;
end;

function TXMLElement.AddElement(const AName: string): TXMLElement;
begin
  Result := TXMLElement.Create(AName);
  FChildren.Add(Result);
end;

function TXMLElement.AddElement(const AName, AText: string): TXMLElement;
begin
  Result := Self.AddElement(AName);
  if AText <> '' then
    Result.AddText(AText);
end;

procedure TXMLElement.AddText(const AText: string);
begin
  FChildren.Add(TXMLText.Create(AText));
end;

procedure TXMLElement.AddCData(const AText: string);
begin
  FChildren.Add(TXMLCData.Create(AText));
end;

procedure TXMLElement.AddComment(const AText: string);
begin
  FChildren.Add(TXMLComment.Create(AText));
end;

{ ---- children: navigation ---- }

function TXMLElement.GetCount: Int;
begin
  Result := FChildren.Count;
end;

function TXMLElement.GetItem(AIndex: Int): TXMLNode;
begin
  Result := FChildren[AIndex];
end;

function TXMLElement.Find(const AName: string): TXMLElement;
var
  I: Int;
  N: TXMLNode;
begin
  Result := nil;
  I := 0;
  while I < FChildren.Count do
  begin
    N := FChildren[I];
    if N.NodeType = xtElement then
      if TXMLElement(N).Name = AName then
      begin
        Result := TXMLElement(N);
        Exit;
      end;
    I := I + 1;
  end;
end;

function TXMLElement.ChildText(const AName: string): string;
var
  E: TXMLElement;
begin
  E := Self.Find(AName);
  if E = nil then
    Result := ''
  else
    Result := E.Text;
end;

function TXMLElement.Elements: TList<TXMLElement>;
var
  I: Int;
  N: TXMLNode;
begin
  Result := TList<TXMLElement>.Create();
  I := 0;
  while I < FChildren.Count do
  begin
    N := FChildren[I];
    if N.NodeType = xtElement then
      Result.Add(TXMLElement(N));
    I := I + 1;
  end;
end;

function TXMLElement.Elements(const AName: string): TList<TXMLElement>;
var
  I: Int;
  N: TXMLNode;
begin
  Result := TList<TXMLElement>.Create();
  I := 0;
  while I < FChildren.Count do
  begin
    N := FChildren[I];
    if N.NodeType = xtElement then
      if TXMLElement(N).Name = AName then
        Result.Add(TXMLElement(N));
    I := I + 1;
  end;
end;

{ ---- children: mutation ---- }

function TXMLElement.Extract(AIndex: Int): TXMLNode;
begin
  Result := FChildren[AIndex];   { hold a ref so it survives the Delete }
  FChildren.Delete(AIndex);
end;

procedure TXMLElement.Delete(AIndex: Int);
begin
  FChildren.Delete(AIndex);
end;

procedure TXMLElement.Clear;
begin
  FChildren.Clear();
end;

{ ---- text ---- }

function TXMLElement.GetText: string;
var
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  XTCollectText(Self, SB);
  Result := SB.ToString();
  SB.Free();
end;

procedure TXMLElement.SetText(const AValue: string);
begin
  FChildren.Clear();
  if AValue <> '' then
    Self.AddText(AValue);
end;

{ ------------------------------------------------------------------ }
{ TXMLDocument                                                       }
{ ------------------------------------------------------------------ }

constructor TXMLDocument.Create;
begin
  FRoot := nil;
  FVersion := '1.0';
  FEncoding := 'UTF-8';
end;

function TXMLDocument.AsXML: string;
var
  W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.Pretty := False;
  W.WriteDeclaration(FVersion, FEncoding);
  if FRoot <> nil then
    FRoot.WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

function TXMLDocument.FormatXML: string;
begin
  Result := FormatXML(2);
end;

function TXMLDocument.FormatXML(AIndent: Int): string;
var
  W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.Pretty := True;
  W.Indent := AIndent;
  W.WriteDeclaration(FVersion, FEncoding);
  if FRoot <> nil then
    FRoot.WriteTo(W);
  Result := W.ToString();
  W.Free();
end;

end.
