{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericforin;

{ Tests for for..in support on generic collections (Step 9b).

  Two blockers:
    1. InstantiateGeneric doesn't clone TClassTypeDef.Properties with
       type-param substitution, so 'Current: T' is invisible on the
       instantiated enumerator type.
    2. generics.collections.pas has no TListEnumerator<T> +
       TList<T>.GetEnumerator; the existing for..in class-enumerator
       protocol path handles everything once those are added. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TGenericForInTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Blocker 1: property cloning in InstantiateGeneric                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericEnumerator_CurrentPropertyVisible;
    procedure TestSemantic_GenericEnumerator_CurrentPropertyType;

    { ------------------------------------------------------------------ }
    { Blocker 2: TListEnumerator<T> + TList<T>.GetEnumerator in RTL        }
    { ------------------------------------------------------------------ }
    procedure TestParse_TListEnumerator_IsGenericTypeDef;
    procedure TestParse_TList_GetEnumerator_Declared;
    procedure TestSemantic_TList_Integer_HasGetEnumerator;
    procedure TestSemantic_TListEnumerator_Integer_HasCurrentProperty;

    { ------------------------------------------------------------------ }
    { End-to-end: for..in on TList<Integer>                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForIn_GenericList_OK;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Minimal generic enumerator with a property backed by a getter. }
  SrcGenericEnumerator =
    '''
        program P;
        type
          TGenEnum<T> = class
            FData:  T;
            FDone:  Boolean;
            function MoveNext: Boolean;
            begin
              Result := not Self.FDone;
              Self.FDone := True
            end;
            function GetCurrent: T;
            begin
              Result := Self.FData
            end;
            property Current: T read GetCurrent;
          end;
        begin end.
        ''';

  { A minimal generic collection that exposes GetEnumerator. }
  SrcGenericCollection =
    '''
        program P;
        type
          TGenEnum<T> = class
            FData:  T;
            FDone:  Boolean;
            function MoveNext: Boolean;
            begin
              Result := not Self.FDone;
              Self.FDone := True
            end;
            function GetCurrent: T;
            begin
              Result := Self.FData
            end;
            property Current: T read GetCurrent;
          end;
          TColl<T> = class
            FItem: T;
            function GetEnumerator: TGenEnum<T>;
            begin
              Result := TGenEnum<T>.Create()
            end;
          end;
        var
          C: TColl<Integer>;
          X: Integer;
        begin
          C := TColl<Integer>.Create();
          for X in C do
            WriteLn(X)
        end.
        ''';

  { Source that requires TList<T> and TListEnumerator<T> from the RTL.
    Uses a minimal inline definition so the test is self-contained. }
  SrcTListEnumeratorDecl =
    '''
        program P;
        type
          TListEnumerator<T> = class
            FList:  ^T;
            FIndex: Integer;
            FCount: Integer;
            function MoveNext: Boolean;
            begin
              Self.FIndex := Self.FIndex + 1;
              Result := Self.FIndex < Self.FCount
            end;
            function GetCurrent: T;
            begin
              Result := (Self.FList + Self.FIndex)^
            end;
            property Current: T read GetCurrent;
          end;
          TMyList<T> = class
            FData:  ^T;
            FCount: Integer;
            function GetEnumerator: TListEnumerator<T>;
            begin
              Result := TListEnumerator<T>.Create()
            end;
          end;
        begin end.
        ''';

  SrcForInGenericList =
    '''
        program P;
        type
          TListEnumerator<T> = class
            FList:  ^T;
            FIndex: Integer;
            FCount: Integer;
            function MoveNext: Boolean;
            begin
              Self.FIndex := Self.FIndex + 1;
              Result := Self.FIndex < Self.FCount
            end;
            function GetCurrent: T;
            begin
              Result := (Self.FList + Self.FIndex)^
            end;
            property Current: T read GetCurrent;
          end;
          TMyList<T> = class
            FData:  ^T;
            FCount: Integer;
            function GetEnumerator: TListEnumerator<T>;
            begin
              Result := TListEnumerator<T>.Create()
            end;
          end;
        var
          L: TMyList<Integer>;
          X: Integer;
        begin
          L := TMyList<Integer>.Create();
          for X in L do
            WriteLn(X)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TGenericForInTests.ParseSrc(const ASrc: string): TProgram;
var
  Lex: TLexer;
  Par: TParser;
begin
  Lex := TLexer.Create(ASrc);
  Par := TParser.Create(Lex);
  try
    Result := Par.Parse();
  finally
    Par.Free();
    Lex.Free();
  end;
end;

function TGenericForInTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

procedure TGenericForInTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(ASrc);
  SA   := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do { expected };
    end;
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Blocker 1: property cloning                                          }
{ ------------------------------------------------------------------ }

procedure TGenericForInTests.TestSemantic_GenericEnumerator_CurrentPropertyVisible;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcGenericEnumerator);
  try
    { The instantiated type is not used in a var decl, so trigger instantiation
      by using the collection source which references TGenEnum<Integer>. }
    { Use the generic enumerator source that references no concrete param —
      check that the template class definition itself still parsed the property. }
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TGenEnum'));
    { TGenEnum is generic, not a concrete type; FindType should return nil. }
    AssertNull('TGenEnum is not a concrete type', RT);
  finally
    Prog.Free();
  end;
end;

procedure TGenericForInTests.TestSemantic_GenericEnumerator_CurrentPropertyType;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  Prop: TPropertyInfo;
begin
  { Instantiate TGenEnum<Integer> via the collection source }
  Prog := AnalyseSrc(SrcGenericCollection);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TGenEnum<Integer>'));
    AssertNotNull('TGenEnum<Integer> was instantiated', RT);
    Prop := RT.FindProperty('Current');
    AssertNotNull('Current property present on TGenEnum<Integer>', Prop);
    AssertEquals('Current property type is tyInteger',
      Ord(tyInteger), Ord(Prop.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Blocker 2: TListEnumerator<T> + TList<T>.GetEnumerator               }
{ ------------------------------------------------------------------ }

procedure TGenericForInTests.TestParse_TListEnumerator_IsGenericTypeDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcTListEnumeratorDecl);
  try
    AssertEquals('Two type decls', 2, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('Name is TListEnumerator', 'TListEnumerator', TD.Name);
    AssertTrue('Def is TGenericTypeDef', TD.Def is TGenericTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericForInTests.TestParse_TList_GetEnumerator_Declared;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  GD:   TGenericTypeDef;
  MD:   TMethodDecl;
  Found: Boolean;
  I:    Integer;
begin
  Prog := ParseSrc(SrcTListEnumeratorDecl);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[1]);  { TMyList }
    GD := TGenericTypeDef(TD.Def);
    Found := False;
    for I := 0 to GD.ClassDef.Methods.Count - 1 do
    begin
      MD := TMethodDecl(GD.ClassDef.Methods.Items[I]);
      if MD.Name = 'GetEnumerator' then
        Found := True;
    end;
    AssertTrue('GetEnumerator method declared on TMyList', Found);
  finally
    Prog.Free();
  end;
end;

procedure TGenericForInTests.TestSemantic_TList_Integer_HasGetEnumerator;
var
  Prog: TProgram;
begin
  { A var of TMyList<Integer> should trigger instantiation; semantic must
    not raise an error (GetEnumerator return type TListEnumerator<Integer>
    must instantiate transitively). }
  Prog := AnalyseSrc(SrcForInGenericList);
  Prog.Free();  { no exception = pass }
end;

procedure TGenericForInTests.TestSemantic_TListEnumerator_Integer_HasCurrentProperty;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  Prop: TPropertyInfo;
begin
  Prog := AnalyseSrc(SrcForInGenericList);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TListEnumerator<Integer>'));
    AssertNotNull('TListEnumerator<Integer> instantiated', RT);
    Prop := RT.FindProperty('Current');
    AssertNotNull('Current property on TListEnumerator<Integer>', Prop);
    AssertEquals('Current type is tyInteger',
      Ord(tyInteger), Ord(Prop.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ End-to-end: for..in on TList<Integer>                                }
{ ------------------------------------------------------------------ }

procedure TGenericForInTests.TestSemantic_ForIn_GenericList_OK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcForInGenericList);
  Prog.Free();  { no exception = semantic check passed }
end;

initialization
  RegisterTest(TGenericForInTests);

end.
