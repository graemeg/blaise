{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.attributes;

{ Tests for the custom attribute system.

  Covers:
    * Parser: [Attr] syntax before class declarations stored on TClassTypeDef
    * Semantic: suffix convention; unknown attribute error; [Weak] unaffected
    * Run time: the attribute tables and the RTTI builtins over them are
      exercised by cp.test.e2e.attributes.

  ProjectRootAttr / RunCmdAttr are still used by cp.test.anonmethods. }

interface

uses
  Classes, SysUtils, Process, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

function ProjectRootAttr: string;
function RunCmdAttr(const AExe: string; const AArgs: array of string): Integer;

type
  TCustomAttributeTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_AttributeOnClass_StoredOnClassTypeDef;
    procedure TestParse_MultipleAttributes_BothStored;
    procedure TestParse_AttributeWithArgs_NameStored;
    procedure TestParse_AttributeArgs_CapturedAsExprs;
    procedure TestParse_MethodAttribute_StoredOnMethodDecl;
    procedure TestParse_NoAttribute_EmptyList;
    procedure TestParse_AttributeOnGenericClass_Stored;

    { Semantic }
    procedure TestSemantic_KnownAttribute_Resolves;
    procedure TestSemantic_SuffixConvention_ThreadedResolvesToThreadedAttribute;
    procedure TestSemantic_UnknownAttribute_RaisesError;
    procedure TestSemantic_UnknownMethodAttribute_RaisesError;
    procedure TestSemantic_WeakOnField_StillWorks;
  end;

implementation

function TCustomAttributeTests.ParseSrc(const ASrc: string): TProgram;
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

function TCustomAttributeTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function ProjectRootAttr: string;
var
  Dir, Parent: string;
  Steps:       Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 6 do
  begin
    if FileExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe/qbe') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

function RunCmdAttr(const AExe: string; const AArgs: array of string): Integer;
var
  Proc: TProcess;
  I:    Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := Low(AArgs) to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    repeat Chunk := Proc.ReadOutput(); until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TCustomAttributeTests.TestParse_AttributeOnClass_StoredOnClassTypeDef;
const
  Src =
    '''
    program P;
    type
      MyAttr = class(TCustomAttribute) end;
      [MyAttr]
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[1]);
    AssertEquals('second type is TFoo', 'TFoo', TD.Name);
    AssertTrue('def is TClassTypeDef', TD.Def is TClassTypeDef);
    CD := TClassTypeDef(TD.Def);
    AssertEquals('one attribute stored', 1, CD.Attributes.Count);
    AssertEquals('attribute name', 'MyAttr', CD.Attributes.Strings[0]);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_MultipleAttributes_BothStored;
const
  Src =
    '''
    program P;
    type
      [AttrA]
      [AttrB]
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('two attributes stored', 2, CD.Attributes.Count);
    AssertEquals('first attr', 'AttrA', CD.Attributes.Strings[0]);
    AssertEquals('second attr', 'AttrB', CD.Attributes.Strings[1]);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_AttributeWithArgs_NameStored;
const
  Src =
    '''
    program P;
    type
      [MyAttr(42, 'hello')]
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('one attribute stored', 1, CD.Attributes.Count);
    AssertEquals('attribute name', 'MyAttr', CD.Attributes.Strings[0]);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_AttributeArgs_CapturedAsExprs;
const
  Src =
    '''
    program P;
    type
      [MyAttr(42, 'hello')]
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  AU:   TAttributeUse;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('one attribute use captured', 1, CD.AttrUses.Count);
    AU := TAttributeUse(CD.AttrUses.Items[0]);
    AssertEquals('use name', 'MyAttr', AU.Name);
    AssertEquals('two argument expressions', 2, AU.Args.Count);
    AssertTrue('first arg is an integer literal',
      TObject(AU.Args.Items[0]) is TIntLiteral);
    AssertTrue('second arg is a string literal',
      TObject(AU.Args.Items[1]) is TStringLiteral);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_MethodAttribute_StoredOnMethodDecl;
const
  Src =
    '''
    program P;
    type
      TFoo = class(TObject)
      published
        [MyAttr('x')]
        [Other]
        procedure Run;
      end;
    begin end.
    ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('one method parsed', 1, CD.Methods.Count);
    MD := TMethodDecl(CD.Methods.Items[0]);
    AssertTrue('method is published', MD.IsPublished);
    AssertEquals('two attribute uses on the method', 2, MD.AttrUses.Count);
    AssertEquals('first use name', 'MyAttr',
      TAttributeUse(MD.AttrUses.Items[0]).Name);
    AssertEquals('first use arg count', 1,
      TAttributeUse(MD.AttrUses.Items[0]).Args.Count);
    AssertEquals('second use name', 'Other',
      TAttributeUse(MD.AttrUses.Items[1]).Name);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_NoAttribute_EmptyList;
const
  Src =
    '''
    program P;
    type
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('no attributes', 0, CD.Attributes.Count);
  finally
    Prog.Free();
  end;
end;

procedure TCustomAttributeTests.TestParse_AttributeOnGenericClass_Stored;
const
  Src =
    '''
    program P;
    type
      [MyAttr]
      TBox<T> = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    AssertTrue('def is TGenericTypeDef',
      TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def is TGenericTypeDef);
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('one attribute on generic class', 1, GD.ClassDef.Attributes.Count);
    AssertEquals('attribute name', 'MyAttr', GD.ClassDef.Attributes.Strings[0]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TCustomAttributeTests.TestSemantic_KnownAttribute_Resolves;
const
  Src =
    '''
    program P;
    type
      MyAttr = class(TCustomAttribute) end;
      [MyAttr]
      TFoo = class(TObject) end;
    begin end.
    ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
  AssertTrue('no semantic error raised', True);
end;

procedure TCustomAttributeTests.TestSemantic_SuffixConvention_ThreadedResolvesToThreadedAttribute;
const
  Src =
    '''
    program P;
    type
      ThreadedAttribute = class(TCustomAttribute) end;
      [Threaded]
      TFoo = class(TObject) end;
    begin end.
    ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
  AssertTrue('suffix convention resolves [Threaded] to ThreadedAttribute', True);
end;

procedure TCustomAttributeTests.TestSemantic_UnknownAttribute_RaisesError;
const
  Src =
    '''
    program P;
    type
      [NonExistent]
      TFoo = class(TObject) end;
    begin end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: Exception do
      if Pos('Unknown attribute', E.Message) >= 0 then
        OK := True;
    on E: TObject do
      if Pos('Unknown attribute', E.ClassName) >= 0 then
        OK := True;
  end;
  AssertTrue('unknown attribute raises semantic error', OK);
end;

procedure TCustomAttributeTests.TestSemantic_UnknownMethodAttribute_RaisesError;
const
  Src =
    '''
    program P;
    type
      TFoo = class(TObject)
      published
        [NonExistent]
        procedure Run;
      end;
    procedure TFoo.Run;
    begin
    end;
    begin end.
    ''';
var
  Prog: TProgram;
  OK:   Boolean;
begin
  OK := False;
  try
    Prog := AnalyseSrc(Src);
    Prog.Free();
  except
    on E: Exception do
      if Pos('Unknown attribute', E.Message) >= 0 then
        OK := True;
    on E: TObject do
      if Pos('Unknown attribute', E.ClassName) >= 0 then
        OK := True;
  end;
  AssertTrue('unknown attribute on a method raises semantic error', OK);
end;

procedure TCustomAttributeTests.TestSemantic_WeakOnField_StillWorks;
const
  Src =
    '''
    program P;
    type
      TFoo = class(TObject)
        [Weak]
        FRef: TObject;
      end;
    begin end.
    ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
  AssertTrue('[Weak] on field still resolves correctly', True);
end;

initialization
  RegisterTest(TCustomAttributeTests);

end.
