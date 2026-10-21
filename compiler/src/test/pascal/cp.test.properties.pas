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
    { a property read through a getter has no storage: it cannot be resized
      by SetLength or passed to a var parameter (both reached the backends and
      failed there); a field-backed property and a field still can }
    procedure TestSem_GetterPropertyIsNotAVariable;
    { an indexed read whose index is a float or a record is the getter CALL
      (Obj.GetP(I)), so the index travels by its ABI class: the backends'
      getter paths carried it in one integer register (arm64 refused it,
      x86-64 crashed on a float literal) }
    procedure TestSem_FloatAndRecordIndexRead_IsGetterCall;
    { properties in records (Delphi/FPC advanced records): parsed into the
      record's property list; a method-backed read and write are the record
      method calls, which take the receiver by address }
    procedure TestParse_RecordProperty;
    procedure TestSem_RecordProperty_AccessIsRecordMethodCall;
    { F()[I] := V writes through the default property of the class or record
      F returns (as FPC and Delphi accept it): the setter call on the result.
      On a record result the setter changes a discarded temporary, so it is
      legal with a warning; storage (an array element) gets none }
    procedure TestSem_DefaultPropWriteOnCallResult_IsSetterCall;
    procedure TestSem_DefaultPropWriteOnRecordTemp_Warns;
    { a FIELD write into a record call result (F().X, F().Inner.X, F().SA[I])
      is lost with the temporary: an error, as in FPC (it compiled silently).
      A dynamic-array element or an object field reached through it is shared
      storage and stays legal; a setter-backed property warns }
    procedure TestSem_FieldWriteOnRecordTemp_IsError;
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

    { ------------------------------------------------------------------ }
    { Indexed-property forms -- P4-7                                      }
    { ------------------------------------------------------------------ }
    { an interface-typed indexed read lowers to the getter CALL, so the
      (obj, itab) result pair takes the method-call path: arm64 rejected
      the read, x86-64 crashed the compiler }
    procedure TestSemantic_InterfaceIndexedPropRead_LowersToGetterCall;
    { P[I] in a method, P an indexed property: Self.P[I].  The bare read
      dropped the index; the bare write did not analyse }
    procedure TestSemantic_ImplicitSelfIndexedProp_ReadAndWrite;
    { R.O[I], O a class field with a default property: the getter runs on
      the FIELD'S value, not on R }
    procedure TestSemantic_FieldDefaultProperty_ReceiverIsField;
    { a Double indexed read calls the getter (x86-64 crashed the compiler) }
    procedure TestCodegen_FloatIndexedPropRead_CallsGetter;
    { TC.A[I], A a static indexed property: the static getter call with the
      index as its argument (the index was dropped -- a garbage read) }
    procedure TestSemantic_StaticIndexedPropRead_PassesIndex;
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

const
  SrcIndexedForms = '''
    program P;
    type
      IFoo = interface function Get: Integer; end;
      THold = class(TObject, IFoo) function Get: Integer; end;
      TObj = class
        FV: IFoo;
        FN: Integer;
        function GetP(I: Integer): IFoo;
        function GetN(I: Integer): Integer;
        procedure SetN(I: Integer; V: Integer);
        property P[I: Integer]: IFoo read GetP;
        property N[I: Integer]: Integer read GetN write SetN; default;
        procedure Run;
      end;
      TRec = record O: TObj; end;
    function THold.Get: Integer; begin Result := 1 end;
    function TObj.GetP(I: Integer): IFoo; begin Result := FV end;
    function TObj.GetN(I: Integer): Integer; begin Result := FN end;
    procedure TObj.SetN(I: Integer; V: Integer); begin FN := V end;
    procedure TObj.Run;
    var L: IFoo; K: Integer;
    begin
      L := P[1];
      K := N[2];
      N[3] := 4
    end;
    var O: TObj; L: IFoo; R: TRec; K: Integer;
    begin
      L := O.P[1];
      K := R.O[2]
    end.
    ''';

{ the analysed body of method AName: the implementation in ProcDecls, or
  the class-body declaration it was attached to }
function FindMethodBody(AProg: TProgram; const AName: string): TBlock;
var
  I, J: Integer;
  MD: TMethodDecl;
  TD: TTypeDecl;
begin
  Result := nil;
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    MD := TMethodDecl(AProg.Block.ProcDecls[I]);
    if SameText(MD.Name, AName) and (MD.Body <> nil) then
      Exit(MD.Body);
  end;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
      begin
        MD := TMethodDecl(TClassTypeDef(TD.Def).Methods[J]);
        if SameText(MD.Name, AName) and (MD.Body <> nil) then
          Exit(MD.Body);
      end;
  end;
end;

procedure TPropertyTests.TestSemantic_InterfaceIndexedPropRead_LowersToGetterCall;
var
  Prog: TProgram;
  Body: TBlock;
  E: TASTExpr;
begin
  Prog := AnalyseSrc(SrcIndexedForms);
  try
    E := TAssignment(Prog.Block.Stmts[0]).Expr;
    AssertTrue('O.P[1] is a method call', E is TMethodCallExpr);
    AssertEquals('getter', 'GetP', TMethodCallExpr(E).Name);
    AssertEquals('index argument', 1, TMethodCallExpr(E).Args.Count);
    Body := FindMethodBody(Prog, 'Run');
    AssertNotNull('TObj.Run body', Body);
    E := TAssignment(Body.Stmts[0]).Expr;
    AssertTrue('P[1] in a method is a method call', E is TMethodCallExpr);
    AssertEquals('getter in a method', 'GetP', TMethodCallExpr(E).Name);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSemantic_ImplicitSelfIndexedProp_ReadAndWrite;
var
  Prog: TProgram;
  Body: TBlock;
  E: TASTExpr;
begin
  Prog := AnalyseSrc(SrcIndexedForms);
  try
    Body := FindMethodBody(Prog, 'Run');
    AssertNotNull('TObj.Run body', Body);
    E := TAssignment(Body.Stmts[1]).Expr;
    AssertTrue('N[2] is the property read', E is TFieldAccessExpr);
    AssertTrue('with its index', TFieldAccessExpr(E).PropIndexExpr <> nil);
    AssertTrue('N[3] := 4 lowers to the setter',
      TStaticSubscriptAssign(Body.Stmts[2]).SetterCall <> nil);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSemantic_FieldDefaultProperty_ReceiverIsField;
var
  Prog: TProgram;
  FA: TFieldAccessExpr;
begin
  Prog := AnalyseSrc(SrcIndexedForms);
  try
    FA := TFieldAccessExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('the default property', 'N', FA.FieldName);
    AssertTrue('read via its getter', FA.PropRead <> nil);
    AssertTrue('on the field read R.O', FA.Base is TFieldAccessExpr);
    AssertEquals('receiver field', 'O', TFieldAccessExpr(FA.Base).FieldName);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestCodegen_FloatIndexedPropRead_CallsGetter;
const
  Src = '''
    program P;
    type
      TObj = class
        FD: Double;
        function GetD(I: Integer): Double;
        property D[I: Integer]: Double read GetD;
      end;
    function TObj.GetD(I: Integer): Double; begin Result := FD end;
    var O: TObj; X: Double;
    begin
      O := TObj.Create();
      X := O.D[1]
    end.
    ''';
begin
  AssertEquals('Double getter called', '',
    AsmMissing(Src, 'callq TObj_GetD', 'bl _TObj_GetD'));
end;

procedure TPropertyTests.TestSemantic_StaticIndexedPropRead_PassesIndex;
const
  Src = '''
    program P;
    type
      TC = class
        static function GetA(I: Integer): Integer;
        static property A[I: Integer]: Integer read GetA;
      end;
    static function TC.GetA(I: Integer): Integer; begin Result := I end;
    var X: Integer;
    begin
      X := TC.A[2]
    end.
    ''';
var
  Prog: TProgram;
  E: TASTExpr;
begin
  Prog := AnalyseSrc(Src);
  try
    E := TAssignment(Prog.Block.Stmts[0]).Expr;
    AssertTrue('TC.A[2] is a method call', E is TMethodCallExpr);
    AssertTrue('a static call', TMethodCallExpr(E).IsStaticCall);
    AssertEquals('getter', 'GetA', TMethodCallExpr(E).Name);
    AssertEquals('index argument', 1, TMethodCallExpr(E).Args.Count);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSem_FloatAndRecordIndexRead_IsGetterCall;
const
  Src = '''
    program P;
    type
      TPair = record A, B: Int64; end;
      TBag = class
        function GetD(D: Double): Integer;
        function GetP(const R: TPair): Integer;
        property ByD[D: Double]: Integer read GetD; default;
        property ByP[const R: TPair]: Integer read GetP;
      end;
    function TBag.GetD(D: Double): Integer; begin Result := Trunc(D) end;
    function TBag.GetP(const R: TPair): Integer; begin Result := R.A end;
    var B: TBag; R: TPair; X: Integer;
    begin
      X := B.ByD[1.5];
      X := B.ByP[R];
      X := B[2.5];
    end.
    ''';
var
  Prog: TProgram;
  E: TASTExpr;
  I: Integer;
begin
  Prog := AnalyseSrc(Src);
  try
    for I := 0 to 2 do
    begin
      E := TAssignment(Prog.Block.Stmts[I]).Expr;
      AssertTrue('statement ' + IntToStr(I) + ' reads through a method call',
        E is TMethodCallExpr);
      AssertEquals('statement ' + IntToStr(I) + ' passes the index', 1,
        TMethodCallExpr(E).Args.Count);
    end;
    AssertEquals('getter', 'GetP',
      TMethodCallExpr(TAssignment(Prog.Block.Stmts[1]).Expr).Name);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestParse_RecordProperty;
var
  Prog: TProgram;
  RD: TRecordTypeDef;
  P: TPropertyDecl;
begin
  Prog := ParseSrc('''
    program P;
    type
      TVec = record
      private
        FX: Integer;
        function GetAt(I: Integer): Integer;
      public
        property X: Integer read FX write FX;
        property At[I: Integer]: Integer read GetAt; default;
        static property Count: Integer read FX;
        Plain: Integer;
      end;
    begin end.
    ''');
  try
    RD := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertEquals('three properties', 3, RD.Properties.Count);
    AssertEquals('the field after them is still a field', 2, RD.Fields.Count);
    P := TPropertyDecl(RD.Properties.Items[1]);
    AssertEquals('indexed', 'I', P.IndexParamName);
    AssertTrue('default', P.IsDefault);
    AssertTrue('static', TPropertyDecl(RD.Properties.Items[2]).IsStatic);
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSem_RecordProperty_AccessIsRecordMethodCall;
const
  Src = '''
    program P;
    type
      TVec = record
      private
        FX: Integer;
        function GetLen: Integer;
        procedure SetX(AV: Integer);
      public
        property X: Integer read FX write SetX;
        property Len: Integer read GetLen;
      end;
    function TVec.GetLen: Integer; begin Result := FX end;
    procedure TVec.SetX(AV: Integer); begin FX := AV end;
    var V: TVec; N: Integer;
    begin
      V.X := 3;
      N := V.Len;
      N := V.X;
    end.
    ''';
var
  Prog: TProgram;
  FA: TFieldAssignment;
  E: TASTExpr;
begin
  Prog := AnalyseSrc(Src);
  try
    FA := TFieldAssignment(Prog.Block.Stmts[0]);
    AssertTrue('V.X := 3 is the setter call', FA.SetterCall is TMethodCallStmt);
    AssertTrue('a record method',
      TMethodDecl(TMethodCallStmt(FA.SetterCall).ResolvedMethod).IsRecordMethod);
    E := TAssignment(Prog.Block.Stmts[1]).Expr;
    AssertTrue('V.Len is the getter call', E is TMethodCallExpr);
    E := TAssignment(Prog.Block.Stmts[2]).Expr;
    AssertTrue('V.X reads the field', (E is TFieldAccessExpr) and
      (TFieldAccessExpr(E).FieldInfo <> nil));
  finally
    Prog.Free();
  end;
end;

const
  DefPropCallResultHead = '''
    program P;
    type
      THolder = class
      private
        FA: array[0..3] of Integer;
        function GetI(I: Integer): Integer;
        procedure SetI(I: Integer; V: Integer);
      public
        property Items[I: Integer]: Integer read GetI write SetI; default;
      end;
      TRec = record
        FA: array[0..3] of Integer;
        function GetI(I: Integer): Integer;
        procedure SetI(I: Integer; V: Integer);
        property Items[I: Integer]: Integer read GetI write SetI; default;
      end;
      TFac = class
        function Get(): THolder;
      end;
    var G: THolder; F: TFac; RA: array[0..1] of TRec;
    function THolder.GetI(I: Integer): Integer; begin Result := FA[I] end;
    procedure THolder.SetI(I: Integer; V: Integer); begin FA[I] := V end;
    function TRec.GetI(I: Integer): Integer; begin Result := FA[I] end;
    procedure TRec.SetI(I: Integer; V: Integer); begin FA[I] := V end;
    function TFac.Get(): THolder; begin Result := G end;
    function MkH(): THolder; begin Result := G end;
    function MkR(): TRec; begin Result.FA[0] := 0 end;
    ''';

procedure TPropertyTests.TestSem_DefaultPropWriteOnCallResult_IsSetterCall;
var
  Prog: TProgram;
  I: Integer;
  SA: TStaticSubscriptAssign;
begin
  Prog := Analyse(DefPropCallResultHead + '''
    begin
      MkH()[0] := 1;
      F.Get()[1] := 2;
      RA[1][2] := 3;
    end.
    ''');
  try
    for I := 0 to 2 do
    begin
      SA := TStaticSubscriptAssign(Prog.Block.Stmts[I]);
      AssertTrue(Format('statement %d is the setter call', [I]),
        SA.SetterCall is TMethodCallStmt);
      AssertEquals(Format('statement %d calls SetI', [I]), 'SetI',
        TMethodCallStmt(SA.SetterCall).Name);
    end;
  finally
    Prog.Free();
  end;
end;

procedure TPropertyTests.TestSem_DefaultPropWriteOnRecordTemp_Warns;
var
  W: string;
begin
  W := SemanticWarnings(DefPropCallResultHead +
    'begin MkR()[0] := 1; end.');
  AssertTrue('a record temporary warns: ' + W,
    Pos('temporary ''TRec'' record is discarded', W) >= 0);
  AssertEquals('a class result and a record element do not warn', '',
    Trim(SemanticWarnings(DefPropCallResultHead +
      'begin MkH()[0] := 1; RA[0][1] := 2; end.')));
end;

procedure TPropertyTests.TestSem_FieldWriteOnRecordTemp_IsError;
const
  Head = '''
    program P;
    type
      TC = class V: Integer; end;
      TIn = record X: Integer; end;
      TRec = record
        DA: array of Integer; SA: array[0..1] of Integer; C: TC; Inner: TIn;
        FP: Integer;
        procedure SetP(A: Integer);
        property P: Integer read FP write SetP;
      end;
    var G: TRec;
    procedure TRec.SetP(A: Integer); begin FP := A end;
    function MkR(): TRec; begin Result := G end;
    ''';
var
  W: string;
begin
  AssertTrue('F().FP := V', Pos('temporary ''TRec'' record',
    SemanticError(Head + 'begin MkR().FP := 1; end.')) >= 0);
  AssertTrue('F().Inner.X := V', Pos('temporary ''TIn'' record',
    SemanticError(Head + 'begin MkR().Inner.X := 1; end.')) >= 0);
  AssertTrue('F().SA[0] := V', Pos('temporary ''TRec'' record',
    SemanticError(Head + 'begin MkR().SA[0] := 1; end.')) >= 0);
  AssertEquals('shared storage through the temporary is legal', '',
    SemanticError(Head + 'begin MkR().DA[0] := 1; MkR().C.V := 2; G.FP := 3; end.'));
  W := SemanticWarnings(Head + 'begin MkR().P := 1; end.');
  AssertTrue('a setter on the temporary warns: ' + W,
    Pos('property ''P'' of a temporary ''TRec'' record is discarded', W) >= 0);
end;

procedure TPropertyTests.TestSem_GetterPropertyIsNotAVariable;
const
  Head = '''
      program P;
      type
        TIA = array of Integer;
        TRows = array of TIA;
        TObj = class
          FRows: TRows;
          FN: Integer;
          function GetRow(I: Integer): TIA;
          function GetN(): Integer;
          property Row[I: Integer]: TIA read GetRow;
          property N: Integer read GetN;
          property NF: Integer read FN write FN;
        end;
      function TObj.GetRow(I: Integer): TIA;
      begin
        Result := FRows[I]
      end;
      function TObj.GetN(): Integer;
      begin
        Result := FN
      end;
      procedure Bump(var X: Integer);
      begin
        X := X + 1
      end;
      var O: TObj;
      begin
      ''';
begin
  AssertTrue('SetLength on an indexed getter property',
    Pos('must be an assignable variable',
      SemanticError(Head + 'SetLength(O.Row[1], 5) end.')) >= 0);
  AssertTrue('a getter property for a var parameter',
    Pos('must be a variable', SemanticError(Head + 'Bump(O.N) end.')) >= 0);
  AssertEquals('a field-backed property and a field are variables', '',
    SemanticError(Head + 'Bump(O.NF); Bump(O.FN); SetLength(O.FRows[1], 2) end.'));
end;

initialization
  RegisterTest(TPropertyTests);

end.
