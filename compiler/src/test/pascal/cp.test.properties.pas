{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.properties;

{ Tests for Pascal property declarations — field-backed and method-backed.
  Properties are transparent syntactic sugar: reads and writes redirect to
  a backing field or method accessor. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TPropertyTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_Property_FieldBackedReadOnly;
    procedure TestParse_Property_FieldBackedReadWrite;
    procedure TestParse_Property_MethodBackedRead;
    procedure TestParse_Property_MethodBackedReadWrite;
    procedure TestParse_Property_CountInClassDef;

    { ------------------------------------------------------------------ }
    { Semantic — field-backed                                              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Property_FieldBacked_OK;
    procedure TestSemantic_Property_FieldBacked_TypeResolved;
    procedure TestSemantic_Property_ReadOnly_WriteRaisesError;
    procedure TestSemantic_Property_ReadWrite_OK;

    { ------------------------------------------------------------------ }
    { Semantic — method-backed                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Property_MethodBacked_OK;
    procedure TestSemantic_Property_MethodBacked_TypeResolved;

    { ------------------------------------------------------------------ }
    { Codegen — field-backed                                               }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — method-backed                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Indexed properties                                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_IndexedProperty_ParamNameAndType;
    procedure TestSemantic_IndexedProperty_Read_OK;
    procedure TestSemantic_IndexedProperty_Write_OK;
    procedure TestSemantic_IndexedProperty_MissingIndex_RaisesError;

    { Default array property: Obj[I] lowers to the getter/setter call. }

    { Regression: 'Outer.Inner.Indexed[Variable]' — chained base + indexed
      property read with a variable index.  Previously crashed the codegen
      because the analyser skipped AnalyseExpr on PropIndexExpr in the
      Base<>nil branch, leaving its ResolvedType nil. }

    { ------------------------------------------------------------------ }
    { Inherited property access — issue #45                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_InheritedProperty_ViaSubclassVar_OK;
    procedure TestSemantic_InheritedProperty_ViaSelf_OK;
    procedure TestSemantic_InheritedProperty_BareIdent_InSubclassMethod_OK;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  SrcFieldBackedReadOnly =
    '''
        program P;
        type
          TBox = class
            FCount: Integer;
            property Count: Integer read FCount;
          end;
        begin
        end.
        ''';

  SrcFieldBackedReadWrite =
    '''
        program P;
        type
          TBox = class
            FValue: Integer;
            property Value: Integer read FValue write FValue;
          end;
        begin
        end.
        ''';

  SrcMethodBackedRead =
    '''
        program P;
        type
          TBox = class
            FCount: Integer;
            function GetCount: Integer;
            begin
              Result := Self.FCount
            end;
            property Count: Integer read GetCount;
          end;
        begin
        end.
        ''';

  SrcMethodBackedReadWrite =
    '''
        program P;
        type
          TBox = class
            FValue: Integer;
            function GetValue: Integer;
            begin
              Result := Self.FValue
            end;
            procedure SetValue(AVal: Integer);
            begin
              Self.FValue := AVal
            end;
            property Value: Integer read GetValue write SetValue;
          end;
        begin
        end.
        ''';

  SrcFieldBackedUsage =
    '''
        program P;
        type
          TBox = class
            FValue: Integer;
            property Value: Integer read FValue write FValue;
          end;
        var B: TBox;
        begin
          B := TBox.Create();
          B.Value := 42;
          WriteLn(B.Value)
        end.
        ''';

  SrcMethodBackedReadUsage =
    '''
        program P;
        type
          TBox = class
            FCount: Integer;
            function GetCount: Integer;
            begin
              Result := Self.FCount
            end;
            property Count: Integer read GetCount;
          end;
        var B: TBox;
        begin
          B := TBox.Create();
          WriteLn(B.Count)
        end.
        ''';

  SrcIndexedPropDecl =
    '''
        program P;
        type
          TList = class
            function Get(AIndex: Integer): Integer;
            begin
              Result := AIndex
            end;
            procedure Put(AIndex: Integer; AValue: Integer);
            begin
            end;
            property Items[Index: Integer]: Integer read Get write Put;
          end;
        begin
        end.
        ''';

  SrcIndexedPropReadUsage =
    '''
        program P;
        type
          TList = class
            function Get(AIndex: Integer): Integer;
            begin
              Result := AIndex
            end;
            property Items[Index: Integer]: Integer read Get;
          end;
        var L: TList; V: Integer;
        begin
          L := TList.Create();
          V := L.Items[3];
          WriteLn(V)
        end.
        ''';

  SrcIndexedPropWriteUsage =
    '''
        program P;
        type
          TList = class
            FValue: Integer;
            function Get(AIndex: Integer): Integer;
            begin
              Result := AIndex
            end;
            procedure Put(AIndex: Integer; AValue: Integer);
            begin
              Self.FValue := AValue
            end;
            property Items[Index: Integer]: Integer read Get write Put;
          end;
        var L: TList;
        begin
          L := TList.Create();
          L.Items[2] := 42
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TPropertyTests.ParseSrc(const ASrc: string): TProgram;
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

function TPropertyTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TPropertyTests.AnalyseExpectError(const ASrc: string);
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
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestParse_Property_FieldBackedReadOnly;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcFieldBackedReadOnly);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Count', PD.Name);
    AssertEquals('type name', 'Integer', PD.TypeName);
    AssertEquals('read name', 'FCount', PD.ReadName);
    AssertEquals('write name empty', '', PD.WriteName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestParse_Property_FieldBackedReadWrite;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcFieldBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Value', PD.Name);
    AssertEquals('read name', 'FValue', PD.ReadName);
    AssertEquals('write name', 'FValue', PD.WriteName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestParse_Property_MethodBackedRead;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcMethodBackedRead);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Count', PD.Name);
    AssertEquals('read name', 'GetCount', PD.ReadName);
    AssertEquals('write name empty', '', PD.WriteName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestParse_Property_MethodBackedReadWrite;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcMethodBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('read name', 'GetValue', PD.ReadName);
    AssertEquals('write name', 'SetValue', PD.WriteName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestParse_Property_CountInClassDef;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcMethodBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one field', 1, CD.Fields.Count);
    AssertEquals('two methods', 2, CD.Methods.Count);
    AssertEquals('one property', 1, CD.Properties.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — field-backed                                              }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestSemantic_Property_FieldBacked_OK;
begin
  AnalyseSrc(SrcFieldBackedReadWrite).Free();
end;

procedure TPropertyTests.TestSemantic_Property_FieldBacked_TypeResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  PI:   TPropertyInfo;
begin
  Prog := AnalyseSrc(SrcFieldBackedReadWrite);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox'));
    AssertNotNull('TBox found', RT);
    PI := RT.FindProperty('Value');
    AssertNotNull('Value property found', PI);
    AssertEquals('type is tyInteger', Ord(tyInteger), Ord(PI.TypeDesc.Kind));
    AssertEquals('read field is FValue', 'FValue', PI.ReadField);
    AssertEquals('write field is FValue', 'FValue', PI.WriteField);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSemantic_Property_ReadOnly_WriteRaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type TBox = class
          FCount: Integer;
          property Count: Integer read FCount;
        end;
        var B: TBox;
        begin B := TBox.Create(); B.Count := 5 end.
        '''
  );
end;

procedure TPropertyTests.TestSemantic_Property_ReadWrite_OK;
begin
  AnalyseSrc(SrcFieldBackedUsage).Free();
end;

{ ------------------------------------------------------------------ }
{ Semantic — method-backed                                             }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestSemantic_Property_MethodBacked_OK;
begin
  AnalyseSrc(SrcMethodBackedReadUsage).Free();
end;

procedure TPropertyTests.TestSemantic_Property_MethodBacked_TypeResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  PI:   TPropertyInfo;
begin
  Prog := AnalyseSrc(SrcMethodBackedRead);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox'));
    PI := RT.FindProperty('Count');
    AssertNotNull('Count property found', PI);
    AssertEquals('type is tyInteger', Ord(tyInteger), Ord(PI.TypeDesc.Kind));
    AssertEquals('read field empty', '', PI.ReadField);
    AssertEquals('read method is GetCount', 'GetCount', PI.ReadMethod);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Indexed properties                                                   }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestParse_IndexedProperty_ParamNameAndType;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcIndexedPropDecl);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Items', PD.Name);
    AssertEquals('index param name', 'Index', PD.IndexParamName);
    AssertEquals('index type name', 'Integer', PD.IndexTypeName);
    AssertEquals('read name', 'Get', PD.ReadName);
    AssertEquals('write name', 'Put', PD.WriteName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_Read_OK;
begin
  AnalyseSrc(SrcIndexedPropReadUsage).Free();
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_Write_OK;
begin
  AnalyseSrc(SrcIndexedPropWriteUsage).Free();
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_MissingIndex_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type TList = class
          function Get(AIndex: Integer): Integer;
          begin Result := AIndex end;
          property Items[Index: Integer]: Integer read Get;
        end;
        var L: TList; V: Integer;
        begin L := TList.Create(); V := L.Items; WriteLn(V) end.
        '''
  );
end;

{ ------------------------------------------------------------------ }
{ Inherited property access — issue #45                                }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestSemantic_InheritedProperty_ViaSubclassVar_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TBase = class
            FCount: Integer;
            property Count: Integer read FCount;
          end;
          TDerived = class(TBase)
          end;
        var
          D: TDerived;
          N: Integer;
        begin
          D := TDerived.Create();
          N := D.Count;
          WriteLn(N)
        end.
        '''
  ).Free();
end;

procedure TPropertyTests.TestSemantic_InheritedProperty_ViaSelf_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TBase = class
            FCount: Integer;
            property Count: Integer read FCount;
          end;
          TDerived = class(TBase)
            function Size: Integer;
          end;
        function TDerived.Size: Integer;
        begin
          Result := Self.Count
        end;
        begin
        end.
        '''
  ).Free();
end;

procedure TPropertyTests.TestSemantic_InheritedProperty_BareIdent_InSubclassMethod_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TBase = class
            FCount: Integer;
            property Count: Integer read FCount;
          end;
          TDerived = class(TBase)
            function Size: Integer;
          end;
        function TDerived.Size: Integer;
        begin
          Result := Count
        end;
        begin
        end.
        '''
  ).Free();
end;

initialization
  RegisterTest(TPropertyTests);

end.
