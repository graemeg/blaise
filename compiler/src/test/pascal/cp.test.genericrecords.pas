{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericrecords;

{ Tests for generic record monomorphization. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TGenericRecordTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_GenericRecord_IsGenericRecordDef;
    procedure TestParse_GenericRecord_ParamName;
    procedure TestParse_GenericRecord_TwoParams;
    procedure TestParse_GenericRecord_FieldUsesTypeParam;
    procedure TestParse_GenericRecord_MethodReturnUsesTypeParam;

    { Semantic — registration and instantiation }
    procedure TestSemantic_GenericRecord_TemplateRegistered;
    procedure TestSemantic_GenericRecord_VarDecl_InstantiatesType;
    procedure TestSemantic_GenericRecord_InstFieldType_Integer;
    procedure TestSemantic_GenericRecord_InstFieldType_String;
    procedure TestSemantic_GenericRecord_TwoParams_BothFieldsResolved;
    procedure TestSemantic_GenericRecord_IsRecordKind;

    { Semantic — out-of-line method implementations }
    procedure TestSemantic_GenericRecord_OutOfLine_MethodLinked;

    { Codegen }
    procedure TestCodegen_GenericRecord_NoTypeInfoEmitted;
    procedure TestCodegen_GenericRecord_NoVTableEmitted;

    { Named type alias for generic record specialisation (issue #124) }
  end;

implementation

const
  SrcGenericRecordOneParam =
    '''
        program Prg;
        type
          TMyVal<T> = record
            Value: T;
          end;
        begin
        end.
        ''';

  SrcGenericRecordTwoParams =
    '''
        program Prg;
        type
          TPair<K, V> = record
            Key: K;
            Val: V;
          end;
        begin
        end.
        ''';

  SrcGenericRecordWithMethod =
    '''
        program Prg;
        type
          TMyVal<T> = record
            Value: T;
            function GetValue: T;
            begin
              Result := Self.Value
            end;
          end;
        var V: TMyVal<Integer>;
        begin
        end.
        ''';

  SrcGenericRecordVarInteger =
    '''
        program Prg;
        type
          TMyVal<T> = record
            Value: T;
          end;
        var V: TMyVal<Integer>;
        begin
          V.Value := 9
        end.
        ''';

  SrcGenericRecordVarString =
    '''
        program Prg;
        type
          TMyVal<T> = record
            Value: T;
          end;
        var S: TMyVal<string>;
        begin
        end.
        ''';

  SrcGenericRecordTwoParamVar =
    '''
        program Prg;
        type
          TPair<K, V> = record
            Key: K;
            Val: V;
          end;
        var P: TPair<string, Integer>;
        begin
        end.
        ''';

  SrcGenericRecordOutOfLineMethod =
    '''
        program Prg;
        type
          TMyVal<T> = record
            FValue: T;
            function GetValue: T;
            procedure SetValue(AValue: T);
          end;

        function TMyVal<T>.GetValue: T;
        begin
          Result := Self.FValue
        end;

        procedure TMyVal<T>.SetValue(AValue: T);
        begin
          Self.FValue := AValue
        end;

        var V: TMyVal<Integer>;
        begin
          V.SetValue(42);
          WriteLn(V.GetValue())
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TGenericRecordTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericRecordTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TGenericRecordTests.TestParse_GenericRecord_IsGenericRecordDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcGenericRecordOneParam);
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('name is TMyVal', 'TMyVal', TD.Name);
    AssertTrue('def is TGenericRecordDef', TD.Def is TGenericRecordDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestParse_GenericRecord_ParamName;
var
  Prog: TProgram;
  GRD:  TGenericRecordDef;
begin
  Prog := ParseSrc(SrcGenericRecordOneParam);
  try
    GRD := TGenericRecordDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one param', 1, GRD.ParamNames.Count);
    AssertEquals('param name is T', 'T', GRD.ParamNames[0]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestParse_GenericRecord_TwoParams;
var
  Prog: TProgram;
  GRD:  TGenericRecordDef;
begin
  Prog := ParseSrc(SrcGenericRecordTwoParams);
  try
    GRD := TGenericRecordDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two params', 2, GRD.ParamNames.Count);
    AssertEquals('first is K', 'K', GRD.ParamNames[0]);
    AssertEquals('second is V', 'V', GRD.ParamNames[1]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestParse_GenericRecord_FieldUsesTypeParam;
var
  Prog: TProgram;
  GRD:  TGenericRecordDef;
  FD:   TFieldDecl;
begin
  Prog := ParseSrc(SrcGenericRecordOneParam);
  try
    GRD := TGenericRecordDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one field', 1, GRD.RecordDef.Fields.Count);
    FD := TFieldDecl(GRD.RecordDef.Fields[0]);
    AssertEquals('field type is T', 'T', FD.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestParse_GenericRecord_MethodReturnUsesTypeParam;
var
  Prog: TProgram;
  GRD:  TGenericRecordDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericRecordWithMethod);
  try
    GRD := TGenericRecordDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one method', 1, GRD.RecordDef.Methods.Count);
    MD := TMethodDecl(GRD.RecordDef.Methods[0]);
    AssertEquals('return type is T', 'T', MD.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TGenericRecordTests.TestSemantic_GenericRecord_TemplateRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericRecordOneParam);
  try
    AssertTrue('template registered',
      Prog.SymbolTable.FindGeneric('TMyVal') is TGenericRecordDef);
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestSemantic_GenericRecord_VarDecl_InstantiatesType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericRecordVarInteger);
  try
    AssertNotNull('type exists',
      Prog.SymbolTable.FindType('TMyVal<Integer>'));
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestSemantic_GenericRecord_InstFieldType_Integer;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericRecordVarInteger);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TMyVal<Integer>'));
    AssertNotNull('RT exists', RT);
    FI := RT.FindField('Value');
    AssertNotNull('Value field exists', FI);
    AssertEquals('field is tyInteger', Ord(tyInteger), Ord(FI.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestSemantic_GenericRecord_InstFieldType_String;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericRecordVarString);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TMyVal<string>'));
    AssertNotNull('RT exists', RT);
    FI := RT.FindField('Value');
    AssertNotNull('Value field exists', FI);
    AssertTrue('field is string', FI.TypeDesc.IsString());
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestSemantic_GenericRecord_TwoParams_BothFieldsResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI0, FI1: TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericRecordTwoParamVar);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPair<string,Integer>'));
    if RT = nil then
      RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPair<string, Integer>'));
    AssertNotNull('RT exists', RT);
    FI0 := RT.FindField('Key');
    FI1 := RT.FindField('Val');
    AssertNotNull('Key exists', FI0);
    AssertNotNull('Val exists', FI1);
    AssertTrue('Key is string', FI0.TypeDesc.IsString());
    AssertEquals('Val is tyInteger', Ord(tyInteger), Ord(FI1.TypeDesc.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TGenericRecordTests.TestSemantic_GenericRecord_IsRecordKind;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(SrcGenericRecordVarInteger);
  try
    TD := Prog.SymbolTable.FindType('TMyVal<Integer>');
    AssertNotNull('type exists', TD);
    AssertTrue('kind is tyRecord', TD.Kind = tyRecord);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TGenericRecordTests.TestSemantic_GenericRecord_OutOfLine_MethodLinked;
var
  Prog: TProgram;
begin
  { Must not raise a semantic error — out-of-line generic record methods must link }
  Prog := AnalyseSrc(SrcGenericRecordOutOfLineMethod);
  try
    AssertNotNull('program analysed without error', Prog);
  finally
    Prog.Free();
  end;
end;

{ A record instance is plain data: neither ISA emits class metadata for it. }
procedure TGenericRecordTests.TestCodegen_GenericRecord_NoTypeInfoEmitted;
begin
  AssertTrue('x86-64: no typeinfo for records',
    Pos('typeinfo_TMyVal', GenAsm(SrcGenericRecordVarInteger, TargetX86_64)) < 0);
  AssertTrue('arm64: no typeinfo for records',
    Pos('typeinfo_TMyVal', GenAsm(SrcGenericRecordVarInteger, TargetArm64)) < 0);
end;

procedure TGenericRecordTests.TestCodegen_GenericRecord_NoVTableEmitted;
begin
  AssertTrue('x86-64: no vtable for records',
    Pos('vtable_TMyVal', GenAsm(SrcGenericRecordVarInteger, TargetX86_64)) < 0);
  AssertTrue('arm64: no vtable for records',
    Pos('vtable_TMyVal', GenAsm(SrcGenericRecordVarInteger, TargetArm64)) < 0);
end;

initialization
  RegisterTest(TGenericRecordTests);

end.
