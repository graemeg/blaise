{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.inlineset;

{ Parser/semantic tests for inline set types: set of <NamedEnum> and
  set of (a, b, c) used directly in a var/param/field position (not only in
  a named type declaration).  E2E coverage (compile + run on both backends)
  lives in cp.test.e2e.inlineset.pas. }

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable;

type
  TInlineSetTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function VarType(P: TProgram; AIndex: Int): TTypeDesc;
  published
    procedure TestSemantic_NamedEnumSet_ResolvesToSet;
    procedure TestSemantic_AnonEnumSet_ResolvesToSet;
    procedure TestSemantic_AnonEnumSet_MembersAreConstants;
    procedure TestSemantic_AnonEnumSet_BaseHasMemberCount;
    procedure TestSemantic_SetMembership_TypeChecks;
    procedure TestSemantic_AnonEnumSet_InParamPosition;
  end;

implementation

function TInlineSetTests.AnalyseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser; A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TInlineSetTests.VarType(P: TProgram; AIndex: Int): TTypeDesc;
begin
  Result := TVarDecl(P.Block.Decls.Items[AIndex]).ResolvedType;
end;

procedure TInlineSetTests.TestSemantic_NamedEnumSet_ResolvesToSet;
var P: TProgram; TD: TTypeDesc;
begin
  P := AnalyseSrc(
    'program X; type TE = (a, b, c); var S: set of TE; begin end.');
  try
    TD := VarType(P, 0);
    AssertNotNull('set type resolved', TD);
    AssertEquals('kind is tySet', Ord(tySet), Ord(TD.Kind));
  finally P.Free(); end;
end;

procedure TInlineSetTests.TestSemantic_AnonEnumSet_ResolvesToSet;
var P: TProgram; TD: TTypeDesc;
begin
  P := AnalyseSrc(
    'program X; var S: set of (red, green, blue); begin end.');
  try
    TD := VarType(P, 0);
    AssertNotNull('set type resolved', TD);
    AssertEquals('kind is tySet', Ord(tySet), Ord(TD.Kind));
  finally P.Free(); end;
end;

procedure TInlineSetTests.TestSemantic_AnonEnumSet_MembersAreConstants;
var P: TProgram;
begin
  { Anonymous enum members must be usable as ordinary enum constants — a set
    literal referencing them must compile. }
  P := AnalyseSrc(
    'program X; var S: set of (red, green, blue); ' +
    'begin S := [red, blue] end.');
  try
    AssertTrue('anon enum members usable in a set literal', True);
  finally P.Free(); end;
end;

procedure TInlineSetTests.TestSemantic_AnonEnumSet_BaseHasMemberCount;
var P: TProgram; TD: TTypeDesc;
begin
  P := AnalyseSrc(
    'program X; var S: set of (one, two, three, four); begin end.');
  try
    TD := VarType(P, 0);
    AssertEquals('kind is tySet', Ord(tySet), Ord(TD.Kind));
    AssertEquals('base enum has 4 members', 4,
      TEnumTypeDesc(TSetTypeDesc(TD).BaseType).Members.Count);
  finally P.Free(); end;
end;

procedure TInlineSetTests.TestSemantic_SetMembership_TypeChecks;
var P: TProgram;
begin
  P := AnalyseSrc(
    'program X; type TE = (a, b); var S: set of TE; r: Boolean; ' +
    'begin S := [a]; r := a in S end.');
  try
    AssertTrue('membership over inline set compiles', True);
  finally P.Free(); end;
end;

procedure TInlineSetTests.TestSemantic_AnonEnumSet_InParamPosition;
var P: TProgram;
begin
  { Inline set in a parameter position resolves the same way as in a var. }
  P := AnalyseSrc(
    'program X; procedure Q(s: set of (lo, hi)); ' +
    'begin if lo in s then end; begin Q([lo]) end.');
  try
    AssertTrue('inline set param compiles', True);
  finally P.Free(); end;
end;

initialization
  RegisterTest(TInlineSetTests);

end.
