{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.arrayofconst;

{ Parser/semantic tests for 'array of const' (heterogeneous variadic
  parameters).  A call-site bracket literal is boxed into an array of the
  intrinsic TVarRec record; the callee receives it as an open array of TVarRec.
  E2E coverage (compile + run on both backends) lives in
  cp.test.e2e.arrayofconst.pas. }

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable;

type
  TArrayOfConstTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AssertFormatRejected(const ASrc: string);
  published
    { Intrinsic TVarRec + vt constants are always available (no uses). }
    procedure TestSemantic_TVarRec_IsIntrinsicRecord;
    procedure TestSemantic_VtConstants_Available;

    { Parsing + parameter typing. }
    procedure TestSemantic_ArrayOfConstParam_IsOpenArrayOfTVarRec;
    procedure TestSemantic_HeterogeneousLiteral_Accepted;
    procedure TestSemantic_LiteralTypedAsArrayOfTVarRec;

    { Format's variadic form takes scalars.  An open or dynamic array of a
      non-TVarRec element is no Format argument: it would be passed as one
      bare pointer and printed (or dereferenced) as garbage.  Only a
      forwarded array of const may stand in for the argument list. }
    procedure TestSemantic_FormatOverOpenArrayOfInteger_Rejected;
    procedure TestSemantic_FormatOverDynArray_Rejected;
    procedure TestSemantic_FormatOverForwardedArrayOfConst_Accepted;
  end;

implementation

function TArrayOfConstTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ ------------------------------------------------------------------ }
{ Intrinsic TVarRec                                                   }
{ ------------------------------------------------------------------ }

procedure TArrayOfConstTests.TestSemantic_TVarRec_IsIntrinsicRecord;
var P: TProgram; Decl: TVarDecl;
begin
  { TVarRec resolves with no uses clause. }
  P := AnalyseSrc('program X; var V: TVarRec; begin end.');
  try
    Decl := TVarDecl(P.Block.Decls.Items[0]);
    AssertNotNull('TVarRec resolved', Decl.ResolvedType);
    AssertEquals('kind tyRecord', Ord(tyRecord), Ord(Decl.ResolvedType.Kind));
    AssertEquals('16-byte layout', 16, Decl.ResolvedType.ByteSize());
  finally P.Free(); end;
end;

procedure TArrayOfConstTests.TestSemantic_VtConstants_Available;
var P: TProgram;
begin
  { vt* constants resolve as ordinary integer constants. }
  P := AnalyseSrc(
    'program X; var I: Integer; ' +
    'begin I := vtInteger + vtAnsiString + vtExtended end.');
  try
    AssertTrue('vt constants available', True);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parameter typing                                                    }
{ ------------------------------------------------------------------ }

procedure TArrayOfConstTests.TestSemantic_ArrayOfConstParam_IsOpenArrayOfTVarRec;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := AnalyseSrc(
    'program X; procedure Foo(args: array of const); begin end; begin end.');
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params.Items[0]);
    AssertTrue('param is open array', Par.IsOpenArray);
    AssertEquals('element type TVarRec', 'TVarRec',
      TOpenArrayTypeDesc(Par.ResolvedType).ElementType.Name);
  finally P.Free(); end;
end;

procedure TArrayOfConstTests.TestSemantic_HeterogeneousLiteral_Accepted;
var P: TProgram;
begin
  { A mixed-type bracket literal is accepted only because the formal is an
    array of const — it would otherwise fail the homogeneity check. }
  P := AnalyseSrc(
    'program X; procedure Foo(args: array of const); begin end; ' +
    'begin Foo([1, ''two'', 3.0, True]) end.');
  try
    AssertTrue('heterogeneous literal accepted', True);
  finally P.Free(); end;
end;

procedure TArrayOfConstTests.TestSemantic_LiteralTypedAsArrayOfTVarRec;
var P: TProgram; Call: TProcCall; Lit: TArrayLiteralExpr;
begin
  P := AnalyseSrc(
    'program X; procedure Foo(args: array of const); begin end; ' +
    'begin Foo([1, ''two'']) end.');
  try
    Call := TProcCall(P.Block.Stmts.Items[0]);
    Lit  := TArrayLiteralExpr(Call.Args.Items[0]);
    AssertTrue('literal flagged IsConstArray', Lit.IsConstArray);
    AssertEquals('typed as array of TVarRec', 'TVarRec',
      TOpenArrayTypeDesc(Lit.ResolvedType).ElementType.Name);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Codegen                                                             }
{ ------------------------------------------------------------------ }

procedure TArrayOfConstTests.AssertFormatRejected(const ASrc: string);
var Raised: Boolean;
begin
  Raised := False;
  try
    AnalyseSrc(ASrc).Free();
  except
    on E: ESemanticError do
    begin
      Raised := True;
      AssertTrue('message names the array argument: ' + E.Message,
        Pos('array of const', E.Message) >= 0);
    end;
  end;
  AssertTrue('Format over a non-TVarRec array is rejected', Raised);
end;

procedure TArrayOfConstTests.TestSemantic_FormatOverOpenArrayOfInteger_Rejected;
begin
  AssertFormatRejected(
    'program X; ' +
    'procedure P(const A: array of Integer); ' +
    'var S: string; begin S := Format(''%d'', A) end; ' +
    'begin P([5, 6]) end.');
end;

procedure TArrayOfConstTests.TestSemantic_FormatOverDynArray_Rejected;
begin
  AssertFormatRejected(
    'program X; var D: array of Integer; S: string; ' +
    'begin SetLength(D, 1); S := Format(''%d %d'', 1, D) end.');
end;

procedure TArrayOfConstTests.TestSemantic_FormatOverForwardedArrayOfConst_Accepted;
begin
  AnalyseSrc(
    'program X; ' +
    'procedure P(const F: string; const A: array of const); ' +
    'var S: string; begin S := Format(F, A) end; ' +
    'begin P(''%d'', [1]) end.').Free();
end;

initialization
  RegisterTest(TArrayOfConstTests);

end.
