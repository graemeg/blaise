{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for the stdlib XML library: Xml.Writer (streaming), Xml.Types
  (DOM), Xml.Parser / Xml.Reader (parsing), and round-tripping through them.
  In-process tests via blaise.testing — no toolchain spawning.

  Self-registers with the test registry via the initialization section; the
  test runner program pulls this unit in (through test.registry) and runs it. }

unit Xml.Tests;

interface

uses
  SysUtils,
  blaise.testing,
  Generics.Collections,
  Xml.Writer,
  Xml.Types,
  Xml.Parser,
  Xml.Reader;

type
  TXmlTests = class(TTestCase)
  published
    { Xml.Writer }
    procedure TestWriter_Element;
    procedure TestWriter_SelfClose;
    procedure TestWriter_Escaping;
    procedure TestWriter_Declaration;
    procedure TestWriter_Pretty;
    procedure TestWriter_CData;
    procedure TestWriter_CDataSplit;
    procedure TestWriter_CommentAndPI;
    procedure TestWriter_WriteElement;
    procedure TestWriter_Errors;
    { Xml.Types (DOM) }
    procedure TestDom_Build;
    procedure TestDom_Pretty;
    procedure TestDom_Attributes;
    procedure TestDom_Navigation;
    procedure TestDom_Text;
    procedure TestDom_Document;
    procedure TestDom_Mutation;
    { Xml.Parser / Xml.Reader }
    procedure TestParse_Simple;
    procedure TestParse_SelfClosing;
    procedure TestParse_Entities;
    procedure TestParse_NumericCharRefs;
    procedure TestParse_CData;
    procedure TestParse_Comments;
    procedure TestParse_Whitespace;
    procedure TestParse_PreserveWhitespace;
    procedure TestParse_DeclarationAndDoctype;
    procedure TestParse_AttributeQuotes;
    procedure TestParse_MismatchedTag;
    procedure TestParse_TwoRoots;
    procedure TestParse_BadEntity;
    procedure TestParse_RoundTrip;
  end;

implementation

{ ---- Xml.Writer ---- }

procedure TXmlTests.TestWriter_Element;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('root');
    W.BeginElement('item');
    W.WriteAttribute('id', '1');
    W.WriteText('x');
    W.EndElement();
  W.EndElement();
  AssertEquals('compact element',
    '<root><item id="1">x</item></root>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_SelfClose;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('a');
    W.BeginElement('br');
    W.EndElement();
    W.BeginElement('img');
    W.WriteAttribute('src', 'p.png');
    W.EndElement();
  W.EndElement();
  AssertEquals('self-closing tags',
    '<a><br/><img src="p.png"/></a>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_Escaping;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('a');
  W.WriteAttribute('q', 'say "hi" & <go>');
  W.WriteText('1 < 2 & 3 > 2');
  W.EndElement();
  AssertEquals('escaped attr and text',
    '<a q="say &quot;hi&quot; &amp; &lt;go&gt;">1 &lt; 2 &amp; 3 &gt; 2</a>',
    W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_Declaration;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.WriteDeclaration();
  W.BeginElement('r');
  W.EndElement();
  AssertEquals('declaration',
    '<?xml version="1.0" encoding="UTF-8"?>' + #10 + '<r/>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_Pretty;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.Pretty := True;
  W.BeginElement('book');
  W.WriteAttribute('id', 'b1');
  W.WriteElement('title', 'Dune');
  W.BeginElement('tags');
  W.WriteElement('tag', 'scifi');
  W.EndElement();
  W.EndElement();
  AssertEquals('pretty output',
    '<book id="b1">' + #10 +
    '  <title>Dune</title>' + #10 +
    '  <tags>' + #10 +
    '    <tag>scifi</tag>' + #10 +
    '  </tags>' + #10 +
    '</book>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_CData;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('s');
  W.WriteCData('a<b>&');
  W.EndElement();
  AssertEquals('cdata verbatim', '<s><![CDATA[a<b>&]]></s>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_CDataSplit;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('s');
  W.WriteCData('x]]>y');
  W.EndElement();
  AssertEquals('cdata terminator split',
    '<s><![CDATA[x]]]]><![CDATA[>y]]></s>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_CommentAndPI;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('a');
  W.WriteComment('note');
  W.WriteProcessingInstruction('php', 'echo');
  W.EndElement();
  AssertEquals('comment and PI', '<a><!--note--><?php echo?></a>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_WriteElement;
var W: TXMLWriter;
begin
  W := TXMLWriter.Create();
  W.BeginElement('book');
  W.WriteElement('title', 'Dune');
  W.WriteElement('subtitle', '');
  W.EndElement();
  AssertEquals('one-shot elements',
    '<book><title>Dune</title><subtitle/></book>', W.ToString());
  W.Free();
end;

procedure TXmlTests.TestWriter_Errors;
var W: TXMLWriter; raised: Boolean;
begin
  W := TXMLWriter.Create();
  raised := False;
  try
    W.WriteAttribute('a', 'b');
  except
    on E: EXMLWriterError do raised := True;
  end;
  AssertTrue('attribute with no open tag raises', raised);
  W.Free();

  W := TXMLWriter.Create();
  raised := False;
  try
    W.EndElement();
  except
    on E: EXMLWriterError do raised := True;
  end;
  AssertTrue('EndElement underflow raises', raised);
  W.Free();

  W := TXMLWriter.Create();
  raised := False;
  try
    W.WriteText('x');
  except
    on E: EXMLWriterError do raised := True;
  end;
  AssertTrue('text outside element raises', raised);
  W.Free();

  W := TXMLWriter.Create();
  W.BeginElement('a');
  W.WriteText('x');
  raised := False;
  try
    W.WriteAttribute('late', '1');
  except
    on E: EXMLWriterError do raised := True;
  end;
  AssertTrue('attribute after content raises', raised);
  W.Free();
end;

{ ---- Xml.Types (DOM) ---- }

procedure TXmlTests.TestDom_Build;
var Lib, Book: TXMLElement;
begin
  Lib := TXMLElement.Create('library');
  Book := Lib.AddElement('book');
  Book.SetAttribute('id', 'b1');
  Book.AddElement('title', 'Dune');
  Book.AddElement('year', '1965');
  AssertEquals('built tree',
    '<library><book id="b1"><title>Dune</title><year>1965</year></book></library>',
    Lib.AsXML());
  Lib.Free();
end;

procedure TXmlTests.TestDom_Pretty;
var Root: TXMLElement;
begin
  Root := TXMLElement.Create('book');
  Root.SetAttribute('id', 'b1');
  Root.AddElement('title', 'Dune');
  AssertEquals('pretty dom',
    '<book id="b1">' + #10 + '  <title>Dune</title>' + #10 + '</book>',
    Root.FormatXML());
  Root.Free();
end;

procedure TXmlTests.TestDom_Attributes;
var E: TXMLElement;
begin
  E := TXMLElement.Create('e');
  AssertFalse('absent', E.HasAttribute('x'));
  AssertEquals('absent get', '', E.GetAttribute('x'));
  E.SetAttribute('x', '1');
  E.SetAttribute('y', '2');
  AssertTrue('present', E.HasAttribute('x'));
  AssertEquals('get', '1', E.GetAttribute('x'));
  AssertEquals('count', 2, E.AttributeCount);
  E.SetAttribute('x', '9');
  AssertEquals('replaced value', '9', E.GetAttribute('x'));
  AssertEquals('replace keeps count', 2, E.AttributeCount);
  AssertEquals('name by index', 'x', E.AttributeName(0));
  AssertEquals('value by index', '2', E.AttributeValue(1));
  E.Attributes['z'] := '3';
  AssertEquals('property read', '3', E.Attributes['z']);
  AssertTrue('remove existing', E.RemoveAttribute('y'));
  AssertFalse('remove absent', E.RemoveAttribute('nope'));
  AssertEquals('count after remove', 2, E.AttributeCount);
  E.Free();
end;

procedure TXmlTests.TestDom_Navigation;
var
  Root, B: TXMLElement;
  L: TList<TXMLElement>;
begin
  Root := TXMLElement.Create('lib');
  Root.AddElement('book', 'A');
  Root.AddElement('book', 'B');
  Root.AddElement('mag', 'M');
  AssertEquals('child count', 3, Root.Count);
  AssertTrue('default items prop', Root[0].NodeType = xtElement);
  B := Root.Find('book');
  AssertEquals('find first', 'A', B.Text);
  AssertTrue('find missing is nil', Root.Find('cd') = nil);
  AssertEquals('childtext', 'M', Root.ChildText('mag'));
  AssertEquals('childtext missing', '', Root.ChildText('cd'));
  L := Root.Elements('book');
  AssertEquals('elements by name', 2, L.Count);
  AssertEquals('elements order', 'B', L[1].Text);
  L.Free();
  L := Root.Elements();
  AssertEquals('all elements', 3, L.Count);
  L.Free();
  Root.Free();
end;

procedure TXmlTests.TestDom_Text;
var P, Bold: TXMLElement;
begin
  P := TXMLElement.Create('p');
  P.AddText('Hello ');
  Bold := P.AddElement('b');
  Bold.AddText('world');
  P.AddText('!');
  AssertEquals('recursive text', 'Hello world!', P.Text);
  AssertEquals('mixed content xml', '<p>Hello <b>world</b>!</p>', P.AsXML());
  P.Text := 'plain';
  AssertEquals('text setter replaces children', '<p>plain</p>', P.AsXML());
  P.Free();
end;

procedure TXmlTests.TestDom_Document;
var Doc: TXMLDocument;
begin
  Doc := TXMLDocument.Create();
  AssertEquals('default version', '1.0', Doc.Version);
  AssertEquals('default encoding', 'UTF-8', Doc.Encoding);
  Doc.Root := TXMLElement.Create('r');
  Doc.Root.SetAttribute('a', '1');
  AssertEquals('document xml',
    '<?xml version="1.0" encoding="UTF-8"?>' + #10 + '<r a="1"/>',
    Doc.AsXML());
  Doc.Free();
end;

procedure TXmlTests.TestDom_Mutation;
var
  E: TXMLElement;
  N: TXMLNode;
begin
  E := TXMLElement.Create('l');
  E.AddElement('a');
  E.AddElement('b');
  E.AddElement('c');
  N := E.Extract(1);
  AssertEquals('extracted node', 'b', TXMLElement(N).Name);
  AssertEquals('after extract', '<l><a/><c/></l>', E.AsXML());
  N.Free();
  E.Delete(0);
  AssertEquals('after delete', '<l><c/></l>', E.AsXML());
  E.Clear();
  AssertEquals('after clear', '<l/>', E.AsXML());
  E.Free();
end;

{ ---- Xml.Parser / Xml.Reader ---- }

procedure TXmlTests.TestParse_Simple;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a x="1"><b>hi</b></a>');
  AssertEquals('root name', 'a', Doc.Root.Name);
  AssertEquals('attribute', '1', Doc.Root.GetAttribute('x'));
  AssertEquals('child text', 'hi', Doc.Root.ChildText('b'));
  Doc.Free();
end;

procedure TXmlTests.TestParse_SelfClosing;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a><b/><c d="2" /></a>');
  AssertEquals('children', 2, Doc.Root.Count);
  AssertEquals('attr on self-closing', '2', Doc.Root.Find('c').GetAttribute('d'));
  Doc.Free();
end;

procedure TXmlTests.TestParse_Entities;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a>&lt;&gt;&amp;&quot;&apos;</a>');
  AssertEquals('named entities', '<>&"''', Doc.Root.Text);
  Doc.Free();
end;

procedure TXmlTests.TestParse_NumericCharRefs;
var
  Doc: TXMLDocument;
  T: string;
  B: Int;
begin
  Doc := GetXML('<a>&#65;&#x42;&#233;</a>');
  T := Doc.Root.Text;
  AssertEquals('decoded length', 4, Length(T));
  B := Byte(T[0]);
  AssertEquals('decimal ref', 65, B);
  B := Byte(T[1]);
  AssertEquals('hex ref', 66, B);
  B := Byte(T[2]);
  AssertEquals('utf8 byte 1', 195, B);
  B := Byte(T[3]);
  AssertEquals('utf8 byte 2', 169, B);
  Doc.Free();
end;

procedure TXmlTests.TestParse_CData;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a><![CDATA[1 < 2 && <tag>]]></a>');
  AssertEquals('cdata content', '1 < 2 && <tag>', Doc.Root.Text);
  AssertTrue('cdata node type', Doc.Root[0].NodeType = xtCData);
  Doc.Free();
end;

procedure TXmlTests.TestParse_Comments;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a><!-- note --><b/></a>');
  AssertEquals('children', 2, Doc.Root.Count);
  AssertTrue('comment node type', Doc.Root[0].NodeType = xtComment);
  AssertEquals('comment value', ' note ', TXMLComment(Doc.Root[0]).Value);
  Doc.Free();
end;

procedure TXmlTests.TestParse_Whitespace;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a>' + #10 + '  <b>x</b>' + #10 + '</a>');
  AssertEquals('whitespace-only text dropped', 1, Doc.Root.Count);
  Doc.Free();
end;

procedure TXmlTests.TestParse_PreserveWhitespace;
var
  P: TXMLParser;
  Doc: TXMLDocument;
begin
  P := TXMLParser.Create('<a> <b/> </a>');
  P.PreserveWhitespace := True;
  Doc := P.Parse();
  AssertEquals('whitespace kept', 3, Doc.Root.Count);
  Doc.Free();
  P.Free();
end;

procedure TXmlTests.TestParse_DeclarationAndDoctype;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<?xml version="1.1" encoding="ASCII"?>'
    + '<!DOCTYPE a [ <!ENTITY x "y"> ]>' + '<a/>');
  AssertEquals('version', '1.1', Doc.Version);
  AssertEquals('encoding', 'ASCII', Doc.Encoding);
  AssertEquals('root after doctype', 'a', Doc.Root.Name);
  Doc.Free();
end;

procedure TXmlTests.TestParse_AttributeQuotes;
var Doc: TXMLDocument;
begin
  Doc := GetXML('<a x=''q"q'' y="a&amp;b"/>');
  AssertEquals('single-quoted attr', 'q"q', Doc.Root.GetAttribute('x'));
  AssertEquals('entity in attr', 'a&b', Doc.Root.GetAttribute('y'));
  Doc.Free();
end;

procedure TXmlTests.TestParse_MismatchedTag;
var Doc: TXMLDocument; raised: Boolean;
begin
  raised := False;
  try
    Doc := GetXML('<a><b></a>');
    Doc.Free();
  except
    on E: EXMLParseError do raised := True;
  end;
  AssertTrue('mismatched closing tag raises', raised);
end;

procedure TXmlTests.TestParse_TwoRoots;
var Doc: TXMLDocument; raised: Boolean;
begin
  raised := False;
  try
    Doc := GetXML('<a/><b/>');
    Doc.Free();
  except
    on E: EXMLParseError do raised := True;
  end;
  AssertTrue('second root raises', raised);
end;

procedure TXmlTests.TestParse_BadEntity;
var Doc: TXMLDocument; raised: Boolean;
begin
  raised := False;
  try
    Doc := GetXML('<a>&bogus;</a>');
    Doc.Free();
  except
    on E: EXMLParseError do raised := True;
  end;
  AssertTrue('unknown entity raises', raised);
end;

procedure TXmlTests.TestParse_RoundTrip;
var
  Doc: TXMLDocument;
  S1: string;
begin
  S1 := '<?xml version="1.0" encoding="UTF-8"?>' + #10 +
    '<library><book id="b1"><title>Dune &amp; more</title>' +
    '<![CDATA[<raw>]]><!--c--></book><empty/></library>';
  Doc := GetXML(S1);
  AssertEquals('round trip', S1, Doc.AsXML());
  Doc.Free();
end;


initialization
  RegisterTest(TXmlTests);

end.
