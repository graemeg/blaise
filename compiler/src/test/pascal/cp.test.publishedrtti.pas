{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.publishedrtti;

{ Tests for Step 11b — published-method RTTI: the parser tagging methods
  declared inside a 'published' visibility section with
  TMethodDecl.IsPublished.  The published-method table and MethodAddress
  are exercised at run time by
  TE2EClasses2Tests.TestRun_MethodAddress_PublishedTable. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST;

type
  TPublishedRTTITests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_Published_Sets_IsPublished;
    procedure TestParse_Public_Does_Not_Set_IsPublished;
    procedure TestParse_PublishedThenPublic_Boundary;
  end;

implementation

function TPublishedRTTITests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TPublishedRTTITests.TestParse_Published_Sets_IsPublished;
const
  Src =
    '''
        program Prg;
        type
          TFoo = class(TObject)
          published
            procedure Bar;
            procedure Baz;
          end;
        procedure TFoo.Bar; begin end;
        procedure TFoo.Baz; begin end;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    CD := TClassTypeDef(TD.Def);
    AssertEquals('two methods', 2, CD.Methods.Count);
    AssertTrue('Bar is published', TMethodDecl(CD.Methods.Items[0]).IsPublished);
    AssertTrue('Baz is published', TMethodDecl(CD.Methods.Items[1]).IsPublished);
  finally
    Prog.Free();
  end;
end;

procedure TPublishedRTTITests.TestParse_Public_Does_Not_Set_IsPublished;
const
  Src =
    '''
        program Prg;
        type
          TFoo = class(TObject)
          public
            procedure Bar;
          end;
        procedure TFoo.Bar; begin end;
        begin end.
        ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertFalse('Bar is not published',
      TMethodDecl(CD.Methods.Items[0]).IsPublished);
  finally
    Prog.Free();
  end;
end;

procedure TPublishedRTTITests.TestParse_PublishedThenPublic_Boundary;
const
  Src =
    '''
        program Prg;
        type
          TFoo = class(TObject)
          published
            procedure InPub;
          public
            procedure InPlain;
          end;
        procedure TFoo.InPub;   begin end;
        procedure TFoo.InPlain; begin end;
        begin end.
        ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertTrue('InPub published',  TMethodDecl(CD.Methods.Items[0]).IsPublished);
    AssertFalse('InPlain not published',
      TMethodDecl(CD.Methods.Items[1]).IsPublished);
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TPublishedRTTITests);
end.
