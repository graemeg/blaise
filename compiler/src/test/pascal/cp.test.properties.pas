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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

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

    { ------------------------------------------------------------------ }
    { Subscript of a property value -- BUG-20261011-prop-value-subscript- }
    { dropped, BUG-20261011-implicit-self-prop-ident                      }
    { ------------------------------------------------------------------ }
    { Obj.Prop[I] on a NON-indexed property subscripts the value: the index
      used to be dropped and the whole string / array came back. }
    procedure TestSemantic_PropertyValueSubscript_ElementType;
    { a field (or field-backed property) of a non-subscriptable type is an
      error, not a silently dropped index }
    procedure TestSemantic_FieldSubscript_NonSubscriptable_RaisesError;
    { P.Y inside a method, P a property of the class: Self.P.Y }
    procedure TestSemantic_ImplicitSelfPropertyBase_FieldRead_OK;
    { a bare property read inside a method dispatches a VIRTUAL getter
      through the vtable on both ISAs (x86-64 called it statically) }
    procedure TestCodegen_ImplicitSelfVirtualGetter_NotStatic;
    { a static-array getter read gets a result buffer: x86-64 passes the
      receiver in %rsi after the sret pointer, arm64 points x8 at a frame
      scratch (both called the getter with no buffer at all) }
    procedure TestCodegen_StaticArrayGetter_SubscriptBase;

    { ------------------------------------------------------------------ }
    { Setter writes -- BUG-20261011-intf-prop-setter,                     }
    { BUG-20261011-implicit-self-prop-write                               }
    { ------------------------------------------------------------------ }
    { a bare property write inside a method: field- and method-backed, and
      a member of a class-typed property (Inner.N := V) }
    procedure TestSemantic_ImplicitSelfPropertyWrite_OK;
    procedure TestSemantic_ImplicitSelfPropertyWrite_ReadOnly_RaisesError;
    { an interface-typed setter receives the (obj, itab) pair: the itab half
      was never loaded, so the setter stored a garbage itab }
    procedure TestCodegen_InterfacePropertySetter_PassesPair;
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

const
  SrcPropValueHolder = '''
    program P;
    type
      TIntArr = array of Integer;
      TStrArr = array of string;
      TSA = array[0..2] of Integer;
      THolder = class
        FS: string;
        FArr: TIntArr;
        FSA: TStrArr;
        FFix: TSA;
        FN: Integer;
        function GetS: string;
        function GetArr: TIntArr;
        function GetSA: TStrArr;
        function GetFix: TSA;
        property S: string read GetS;
        property SF: string read FS;
        property Arr: TIntArr read GetArr;
        property SA: TStrArr read GetSA;
        property Fix: TSA read GetFix;
        property NF: Integer read FN;
      end;
    function THolder.GetS: string; begin Result := FS end;
    function THolder.GetArr: TIntArr; begin Result := FArr end;
    function THolder.GetSA: TStrArr; begin Result := FSA end;
    function THolder.GetFix: TSA; begin Result := FFix end;
    var H: THolder; I: Integer; X: string;
    begin
      H := THolder.Create();
      %s
    end.
    ''';

procedure TPropertyTests.TestSemantic_PropertyValueSubscript_ElementType;
begin
  AssertEquals('element types of property-value subscripts', '',
    SemanticError(Format(SrcPropValueHolder,
      ['I := H.S[1]; I := H.SF[1]; I := H.Arr[1]; X := H.SA[0]; ' +
       'I := H.Fix[2]; I := (H.S)[0]'])));
end;

procedure TPropertyTests.TestSemantic_FieldSubscript_NonSubscriptable_RaisesError;
begin
  AssertTrue('Integer field subscript is rejected',
    Pos('cannot be subscripted',
      SemanticError(Format(SrcPropValueHolder, ['I := H.FN[1]']))) >= 0);
  AssertTrue('Integer field-backed property subscript is rejected',
    SemanticError(Format(SrcPropValueHolder, ['I := H.NF[1]'])) <> '');
end;

const
  SrcImplicitSelfProps = '''
    program P;
    type
      TPt = record X, Y: Integer; end;
      TBase = class
        FP: TPt;
        function GetP: TPt;
        function GetN: Integer; virtual;
        property P: TPt read GetP;
        property N: Integer read GetN;
        procedure Show;
      end;
      TKid = class(TBase)
        function GetN: Integer; override;
      end;
    function TBase.GetP: TPt; begin Result := FP end;
    function TBase.GetN: Integer; begin Result := 1 end;
    function TKid.GetN: Integer; begin Result := 2 end;
    procedure TBase.Show;
    begin
      WriteLn(P.Y, N)
    end;
    begin
      TKid.Create().Show()
    end.
    ''';

procedure TPropertyTests.TestSemantic_ImplicitSelfPropertyBase_FieldRead_OK;
begin
  AssertEquals('P.Y with P an implicit-Self property', '',
    SemanticError(SrcImplicitSelfProps));
end;

procedure TPropertyTests.TestCodegen_ImplicitSelfVirtualGetter_NotStatic;
begin
  AssertTrue('x86-64: GetN is not called statically',
    Pos(#9'callq TBase_GetN', GenAsm(SrcImplicitSelfProps, TargetX86_64)) < 0);
  AssertTrue('arm64: GetN is not called statically',
    Pos(#9'bl _TBase_GetN', GenAsm(SrcImplicitSelfProps, TargetArm64)) < 0);
end;

procedure TPropertyTests.TestCodegen_StaticArrayGetter_SubscriptBase;
const
  Src = '''
    program P;
    type
      TSA = array[0..2] of Integer;
      TC = class
        FSA: TSA;
        function GetSA: TSA;
        property SA: TSA read GetSA;
      end;
    function TC.GetSA: TSA; begin Result := FSA end;
    var O: TC;
    begin
      O := TC.Create();
      WriteLn(O.SA[1])
    end.
    ''';
begin
  AssertEquals('static-array getter as a subscript base', '',
    AsmMissing(Src, 'movq O(%rip), %rsi',
      'ldr x0, [x9, _g_O@PAGEOFF]' + #10#9 + 'sub x8, x29, #'));
end;

const
  SrcBareWrites = '''
    program P;
    type
      TInner = class
        FN: Integer;
        procedure SetN(V: Integer);
        property N: Integer read FN write SetN;
      end;
      TC = class
        FM: Integer;
        FIn: TInner;
        procedure SetK(V: Integer);
        property K: Integer read FM write SetK;
        property M: Integer read FM write FM;
        property Inner: TInner read FIn;
        property RO: Integer read FM;
        procedure Go;
      end;
    procedure TInner.SetN(V: Integer); begin FN := V end;
    procedure TC.SetK(V: Integer); begin FM := V end;
    procedure TC.Go;
    begin
      %s
    end;
    begin
    end.
    ''';

procedure TPropertyTests.TestSemantic_ImplicitSelfPropertyWrite_OK;
begin
  AssertEquals('bare property writes inside a method', '',
    SemanticError(Format(SrcBareWrites, ['K := 1; M := 2; Inner.N := 3'])));
end;

procedure TPropertyTests.TestSemantic_ImplicitSelfPropertyWrite_ReadOnly_RaisesError;
begin
  AssertTrue('a read-only property is rejected',
    Pos('read-only', SemanticError(Format(SrcBareWrites, ['RO := 1']))) >= 0);
end;

procedure TPropertyTests.TestCodegen_InterfacePropertySetter_PassesPair;
const
  Src = '''
    program P;
    type
      IThing = interface
        function Val: Integer;
      end;
      TThing = class(TObject, IThing)
        function Val: Integer;
      end;
      THolder = class
        FThing: IThing;
        procedure SetThing(V: IThing);
        property Thing: IThing read FThing write SetThing;
      end;
    function TThing.Val: Integer; begin Result := 1 end;
    procedure THolder.SetThing(V: IThing); begin FThing := V end;
    var H: THolder; T: IThing;
    begin
      H := THolder.Create();
      T := TThing.Create();
      H.Thing := T
    end.
    ''';
begin
  AssertEquals('setter(Self, obj, itab)', '',
    AsmMissing(Src,
      'movq T_itab(%rip), %rcx',
      'ldr x2, [sp], #16' + #10#9 + 'ldr x1, [sp], #16' + #10#9 +
      'ldr x0, [sp], #16' + #10#9 + 'bl _THolder_SetThing'));
end;

initialization
  RegisterTest(TPropertyTests);

end.
