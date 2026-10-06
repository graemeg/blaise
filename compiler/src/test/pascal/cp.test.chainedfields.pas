{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.chainedfields;

{ Tests for chained field access expressions: A.B.C and deeper. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TChainedFieldTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestParse_TwoDots_HasBase;
    procedure TestParse_ThreeDots_HasNestedBases;
    procedure TestSemantic_RecordChain_ResolvesToInnerType;
    procedure TestSemantic_ClassFieldThenRecordField_Resolves;
  end;

implementation

function TChainedFieldTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TChainedFieldTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

const
  SrcTwoDeep =
    '''
        program P;
        type
          TInner = record
            Value: Integer;
          end;
          TOuter = record
            Inner: TInner;
          end;
        var O: TOuter; N: Integer;
        begin
          N := O.Inner.Value
        end.
        ''';

  SrcThreeDeep =
    '''
        program P;
        type
          TA = record X: Integer; end;
          TB = record A: TA; end;
          TC = record B: TB; end;
        var C: TC; N: Integer;
        begin
          N := C.B.A.X
        end.
        ''';

  SrcClassFieldOfRecord =
    '''
        program P;
        type
          TThing = class(TObject)
            Inner: Integer;
          end;
          TBox = record
            Thing: TThing;
          end;
        var B: TBox; N: Integer; T: TThing;
        begin
          B.Thing := TThing.Create();
          N := B.Thing.Inner;
          T := B.Thing;
          T.Free()
        end.
        ''';

procedure TChainedFieldTests.TestParse_TwoDots_HasBase;
var Prog: TProgram; Assn: TAssignment; Fld: TFieldAccessExpr;
begin
  Prog := ParseSrc(SrcTwoDeep);
  try
    Assn := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is field access', Assn.Expr is TFieldAccessExpr);
    Fld := TFieldAccessExpr(Assn.Expr);
    AssertEquals('outer field name', 'Value', Fld.FieldName);
    AssertNotNull('has Base', Fld.Base);
    AssertTrue('base is field access', Fld.Base is TFieldAccessExpr);
    AssertEquals('inner field name', 'Inner',
      TFieldAccessExpr(Fld.Base).FieldName);
  finally Prog.Free(); end;
end;

procedure TChainedFieldTests.TestParse_ThreeDots_HasNestedBases;
var Prog: TProgram; Assn: TAssignment; Fld: TFieldAccessExpr;
begin
  Prog := ParseSrc(SrcThreeDeep);
  try
    Assn := TAssignment(Prog.Block.Stmts[0]);
    Fld := TFieldAccessExpr(Assn.Expr);
    AssertEquals('leaf field', 'X', Fld.FieldName);
    AssertTrue('base 1 is field access', Fld.Base is TFieldAccessExpr);
    AssertEquals('mid field', 'A', TFieldAccessExpr(Fld.Base).FieldName);
    AssertTrue('base 2 is field access',
      TFieldAccessExpr(Fld.Base).Base is TFieldAccessExpr);
    AssertEquals('base field', 'B',
      TFieldAccessExpr(TFieldAccessExpr(Fld.Base).Base).FieldName);
  finally Prog.Free(); end;
end;

procedure TChainedFieldTests.TestSemantic_RecordChain_ResolvesToInnerType;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcTwoDeep);
  try
    Assn := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('chain type is Integer',
      Ord(tyInteger), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

procedure TChainedFieldTests.TestSemantic_ClassFieldThenRecordField_Resolves;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcClassFieldOfRecord);
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

initialization
  RegisterTest(TChainedFieldTests);

end.
