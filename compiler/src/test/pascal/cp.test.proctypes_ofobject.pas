{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.proctypes_ofobject;

{ Tests for Step 11c — 'procedure of object' method-pointer types and the
  TMethod intrinsic record.

  Layout: a method-pointer value is a 16-byte block, Code at offset 0 and
  Data (Self) at offset 8.  This matches TMethod byte-for-byte; the cast
  TMyMethod(m) is a reinterpretation.  A method-pointer call site loads both
  halves and calls Code with Data as Self.  Run-time coverage lives in
  cp.test.e2e.classes2 (TestRun_MethodPtr*). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TProcTypesOfObjectTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_OfObject_SetsIsMethodPtr;
    procedure TestParse_BareProcType_LeavesIsMethodPtrFalse;
    procedure TestParse_FunctionOfObject_AcceptsReturnType;

    { Semantic / Symbol Table }
    procedure TestSemantic_TMethod_IsRegistered;
    procedure TestSemantic_TMethod_HasCodeAndDataFields;
    procedure TestSemantic_MethodPtr_PropagatesIsMethodPtr;

    { Codegen }
    procedure TestSemantic_MethodPtr_ByteSizeIs16;
    procedure TestSemantic_BareProcPtr_ByteSizeIs8;
  end;

implementation

function TProcTypesOfObjectTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcTypesOfObjectTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ ------------------------------------------------------------------ }
{  Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestParse_OfObject_SetsIsMethodPtr;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    TD  := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    Def := TProceduralTypeDef(TD.Def);
    AssertTrue('IsMethodPtr is True for "of object" type', Def.IsMethodPtr);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestParse_BareProcType_LeavesIsMethodPtrFalse;
const
  Src =
    '''
        program P;
        type TP = procedure;
        begin end.
        ''';
var
  Def: TProceduralTypeDef;
begin
  Def := TProceduralTypeDef(TTypeDecl(ParseSrc(Src).Block.TypeDecls.Items[0]).Def);
  AssertFalse('IsMethodPtr is False for bare procedural type', Def.IsMethodPtr);
end;

procedure TProcTypesOfObjectTests.TestParse_FunctionOfObject_AcceptsReturnType;
const
  Src =
    '''
        program P;
        type TF = function (X: Integer): Integer of object;
        begin end.
        ''';
var
  Def: TProceduralTypeDef;
begin
  Def := TProceduralTypeDef(TTypeDecl(ParseSrc(Src).Block.TypeDecls.Items[0]).Def);
  AssertTrue('IsFunction set',   Def.IsFunction);
  AssertTrue('IsMethodPtr set',  Def.IsMethodPtr);
  AssertEquals('return type',    'Integer', Def.ReturnTypeName);
end;

{ ------------------------------------------------------------------ }
{  Semantic / Symbol Table                                             }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestSemantic_TMethod_IsRegistered;
const
  Src =
    '''
        program P;
        var M: TMethod;
        begin end.
        ''';
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertNotNull('TMethod resolves',         VD.ResolvedType);
    AssertEquals('TMethod kind is tyRecord',  Ord(tyRecord), Ord(VD.ResolvedType.Kind));
    AssertEquals('TMethod name',              'TMethod',     VD.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_TMethod_HasCodeAndDataFields;
const
  Src =
    '''
        program P;
        var M: TMethod;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertNotNull('Code field exists', RT.FindField('Code'));
    AssertNotNull('Data field exists', RT.FindField('Data'));
    AssertEquals('Code at offset 0', 0, RT.FindField('Code').Offset);
    AssertEquals('Data at offset 8', 8, RT.FindField('Data').Offset);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_MethodPtr_PropagatesIsMethodPtr;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin end.
        ''';
var
  Prog:     TProgram;
  ProcDesc: TProceduralTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    ProcDesc := TProceduralTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertTrue('IsMethodPtr propagated to type descriptor',
      ProcDesc.IsMethodPtr);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  End-to-end                                                          }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestSemantic_MethodPtr_ByteSizeIs16;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TD := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertEquals('IsMethodPtr ByteSize is 16', 16, TD.ByteSize());
    AssertEquals('IsMethodPtr RawSize is 16',  16, TD.RawSize());
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_BareProcPtr_ByteSizeIs8;
const
  Src =
    '''
        program P;
        type TP = procedure;
        var G: TP;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TD := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertEquals('bare procedural ByteSize stays 8', 8, TD.ByteSize());
    AssertEquals('bare procedural RawSize stays 8',  8, TD.RawSize());
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TProcTypesOfObjectTests);
end.
