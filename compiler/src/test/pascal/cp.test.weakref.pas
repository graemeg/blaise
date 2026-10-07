{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the [Weak] attribute: zeroing weak references used to break
  reference cycles under universal ARC.  Organised in the order the
  feature is implemented:

    1. Lexer    — tkLBracket / tkRBracket token recognition.
    2. Parser   — [Ident] attribute list before var and field decls.
    3. Semantic — resolve WeakAttribute (with suffix fallback) and flag
                  the declaration; reject on non-reference types.
    4. Codegen  — weak vars use _WeakAssign / _WeakClear at every ARC
                  insertion site (run-time coverage:
                  TE2EArcTests.TestRun_WeakAndUnretained_NonOwning).
    5. E2E      — parent/child cycle that leaks without [Weak] and is
                  valgrind-clean with it.

  Each section is driven by a TDD cycle: failing test first, then the
  minimum code change to pass it.  When tests in a section pass, they
  act as a regression fence for later work. }

unit cp.test.weakref;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TWeakRefTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc, AExpectedFragment: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer — bracket tokens                                               }
    { ------------------------------------------------------------------ }
    procedure TestLex_LBracket;
    procedure TestLex_RBracket;

    { ------------------------------------------------------------------ }
    { Parser — attribute list on var and field declarations                }
    { ------------------------------------------------------------------ }
    procedure TestParse_WeakAttribute_OnVarDecl;
    procedure TestParse_WeakAttribute_OnClassField;
    procedure TestParse_UnknownAttribute_AcceptedSilently;
    procedure TestParse_MultipleAttributes_OnVar;

    { ------------------------------------------------------------------ }
    { Semantic — name resolution + type validation                         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Weak_OnClassVar_OK;
    procedure TestSemantic_Weak_OnInterfaceVar_OK;
    procedure TestSemantic_Weak_OnInteger_RaisesError;
    procedure TestSemantic_Weak_OnString_RaisesError;
    procedure TestSemantic_WeakAttribute_SuffixMatches_Weak;

    { ------------------------------------------------------------------ }
    { [Unretained] — non-owning, no ARC, no weak registry                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Unretained_OnInteger_RaisesError;
    procedure TestSemantic_Unretained_WithWeak_RaisesError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TWeakRefTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TWeakRefTests.AnalyseSrc(const ASrc: string): TProgram;
var
  Prog:     TProgram;
  Analyser: TSemanticAnalyser;
begin
  Prog     := ParseSrc(ASrc);
  Analyser := TSemanticAnalyser.Create();
  try
    Analyser.Analyse(Prog);
    Result := Prog;
  finally
    Analyser.Free();
  end;
end;

procedure TWeakRefTests.AnalyseExpectError(const ASrc, AExpectedFragment: string);
var
  Raised: Boolean;
  Msg:    string;
begin
  Raised := False;
  Msg    := '';
  try
    AnalyseSrc(ASrc).Free();
  except
    on E: ESemanticError do
    begin
      Raised := True;
      Msg    := E.FMessage;
    end;
  end;
  AssertTrue('expected ESemanticError', Raised);
  AssertTrue(
    Format('error message ''%s'' did not contain ''%s''', [Msg, AExpectedFragment]),
    Pos(LowerCase(AExpectedFragment), LowerCase(Msg)) > 0);
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TWeakRefTests.TestLex_LBracket;
var
  L:   TLexer;
  Tok: TToken;
begin
  L := TLexer.Create('[');
  try
    Tok := L.Next();
    AssertEquals('kind is tkLBracket', Ord(tkLBracket), Ord(Tok.Kind));
  finally
    L.Free();
  end;
end;

procedure TWeakRefTests.TestLex_RBracket;
var
  L:   TLexer;
  Tok: TToken;
begin
  L := TLexer.Create(']');
  try
    Tok := L.Next();
    AssertEquals('kind is tkRBracket', Ord(tkRBracket), Ord(Tok.Kind));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

const
  SrcWeakOnVar =
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var
          [Weak] F: TFoo;
        begin
        end.
        ''';

  SrcWeakOnField =
    '''
        program P;
        type
          TParent = class
          end;
          TChild = class
            [Weak] Parent: TParent;
          end;
        begin
        end.
        ''';

  SrcUnknownAttr =
    '''
        program P;
        type
          TFoo = class
          end;
        var
          [SomeUnknown] F: TFoo;
        begin
        end.
        ''';

  SrcMultiAttr =
    '''
        program P;
        type
          TFoo = class
          end;
        var
          [Weak][SomeOther] F: TFoo;
        begin
        end.
        ''';

procedure TWeakRefTests.TestParse_WeakAttribute_OnVarDecl;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcWeakOnVar);
  try
    AssertEquals('one var decl in block', 1, Prog.Block.Decls.Count);
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertNotNull('attributes list allocated', VD.Attributes);
    AssertTrue('Weak attribute recorded',
      VD.Attributes.IndexOf('Weak') >= 0);
  finally
    Prog.Free();
  end;
end;

procedure TWeakRefTests.TestParse_WeakAttribute_OnClassField;
var
  Prog:  TProgram;
  TD:    TTypeDecl;
  Cls:   TClassTypeDef;
  FDecl: TFieldDecl;
  I:     Integer;
begin
  Prog := ParseSrc(SrcWeakOnField);
  try
    { Locate TChild among the type decls and pull its Parent field. }
    TD  := nil;
    for I := 0 to Prog.Block.TypeDecls.Count - 1 do
      if SameText(TTypeDecl(Prog.Block.TypeDecls[I]).Name, 'TChild') then
      begin
        TD := TTypeDecl(Prog.Block.TypeDecls[I]);
        Break;
      end;
    AssertNotNull('TChild declared', TD);
    Cls := TClassTypeDef(TD.Def);
    AssertEquals('TChild has one field', 1, Cls.Fields.Count);
    FDecl := TFieldDecl(Cls.Fields[0]);
    AssertNotNull('field attributes allocated', FDecl.Attributes);
    AssertTrue('Weak attribute recorded on field',
      FDecl.Attributes.IndexOf('Weak') >= 0);
  finally
    Prog.Free();
  end;
end;

procedure TWeakRefTests.TestParse_UnknownAttribute_AcceptedSilently;
var
  Prog: TProgram;
begin
  { Parser must accept attributes it doesn't recognise — forward-compatibility
    with user-defined attributes.  Recording the name is sufficient. }
  Prog := ParseSrc(SrcUnknownAttr);
  try
    AssertEquals('one var decl parsed despite unknown attr',
      1, Prog.Block.Decls.Count);
    AssertTrue('attribute name captured',
      TVarDecl(Prog.Block.Decls[0]).Attributes.IndexOf('SomeUnknown') >= 0);
  finally
    Prog.Free();
  end;
end;

procedure TWeakRefTests.TestParse_MultipleAttributes_OnVar;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcMultiAttr);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('Weak recorded',      VD.Attributes.IndexOf('Weak') >= 0);
    AssertTrue('SomeOther recorded', VD.Attributes.IndexOf('SomeOther') >= 0);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

const
  SrcSemWeakClassVar =
    '''
        program P;
        type
          TFoo = class
          end;
        var
          [Weak] F: TFoo;
        begin
        end.
        ''';

  SrcSemWeakInterfaceVar =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
        var
          [Weak] F: IFoo;
        begin
        end.
        ''';

  SrcSemWeakInt =
    '''
        program P;
        var
          [Weak] N: Integer;
        begin
        end.
        ''';

  SrcSemWeakString =
    '''
        program P;
        var
          [Weak] S: string;
        begin
        end.
        ''';

  SrcSemWeakSuffix =
    '''
        program P;
        type
          TFoo = class
          end;
        var
          [WeakAttribute] F: TFoo;
        begin
        end.
        ''';

procedure TWeakRefTests.TestSemantic_Weak_OnClassVar_OK;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcSemWeakClassVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak flag set on class var', VD.IsWeak);
  finally
    Prog.Free();
  end;
end;

procedure TWeakRefTests.TestSemantic_Weak_OnInterfaceVar_OK;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcSemWeakInterfaceVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak flag set on interface var', VD.IsWeak);
  finally
    Prog.Free();
  end;
end;

procedure TWeakRefTests.TestSemantic_Weak_OnInteger_RaisesError;
begin
  AnalyseExpectError(SrcSemWeakInt, 'weak');
end;

procedure TWeakRefTests.TestSemantic_Weak_OnString_RaisesError;
begin
  AnalyseExpectError(SrcSemWeakString, 'weak');
end;

procedure TWeakRefTests.TestSemantic_WeakAttribute_SuffixMatches_Weak;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  { [WeakAttribute] is the long form; the compiler must resolve it the
    same way as [Weak] by stripping the 'Attribute' suffix. }
  Prog := AnalyseSrc(SrcSemWeakSuffix);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak set via long form', VD.IsWeak);
  finally
    Prog.Free();
  end;
end;

const
  { [Unretained] on a non-class field is rejected. }
  SrcSemUnretainedInt =
    '''
        program P;
        type
          TFoo = class
            [Unretained] N: Integer;
          end;
        begin
        end.
        ''';

  { [Weak] and [Unretained] together is rejected. }
  SrcSemUnretainedWithWeak =
    '''
        program P;
        type
          TFoo = class
          end;
          TBar = class
            [Weak][Unretained] F: TFoo;
          end;
        begin
        end.
        ''';

procedure TWeakRefTests.TestSemantic_Unretained_OnInteger_RaisesError;
begin
  AnalyseExpectError(SrcSemUnretainedInt, 'Unretained');
end;

procedure TWeakRefTests.TestSemantic_Unretained_WithWeak_RaisesError;
begin
  AnalyseExpectError(SrcSemUnretainedWithWeak, 'mutually exclusive');
end;

initialization
  RegisterTest(TWeakRefTests);

end.
