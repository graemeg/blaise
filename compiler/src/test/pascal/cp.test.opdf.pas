{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.opdf;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uDebugOPDF, uDebugFacts;

type
  TOPDFTests = class(TTestCase)
  private
    function GenOPDF(const ASrc: string): string;
    function Contains(const AText, AFragment: string): Boolean;
  published
    procedure TestOPDF_SectionDeclaration;
    procedure TestOPDF_HeaderMagic;
    procedure TestOPDF_HeaderVersion;
    procedure TestOPDF_TotalRecordsStreamTerminated;
    procedure TestOPDF_Primitive_Integer;
    procedure TestOPDF_Primitive_Boolean;
    procedure TestOPDF_Primitive_Int64;
    procedure TestOPDF_Primitive_Double_SubKindFloat;
    procedure TestOPDF_Primitive_Single_SubKindFloat;
    procedure TestOPDF_AnsiStr_Record;
    { A string constant whose value contains a double-quote, newline or
      backslash must be C-escaped in the recConstant `.ascii` line, else the
      literal closes early and the assembler sees a garbage mnemonic. }
    procedure TestOPDF_StringConst_SpecialChars_Escaped;
    procedure TestOPDF_GlobalVar_QuadLabel;
    procedure TestOPDF_GlobalVar_RecType;
    procedure TestOPDF_Enum_RecType;
    procedure TestOPDF_Enum_MemberName;
    procedure TestOPDF_Class_RecType;
    procedure TestOPDF_Class_VtableRef;
    procedure TestOPDF_FunctionScope_RecType;
    procedure TestOPDF_MethodScope_Emitted;
    procedure TestOPDF_DestructorScope_Emitted;
    { Facts-driven emission (native backend): exact HighPC end labels, real
      RBP offsets, per-statement line records. }
    procedure TestOPDF_Facts_ExactScopeAndLocals;
    procedure TestOPDF_Facts_PerStatementLines;
    procedure TestOPDF_FunctionScope_LowPC;
    procedure TestOPDF_Parameter_RecType;
    procedure TestOPDF_LocalVar_RecType;
    procedure TestOPDF_LocalVar_RBPOffset;
    procedure TestOPDF_LineInfo_RecType;
    procedure TestOPDF_LineInfo_FileName;
    procedure TestOPDF_LineInfo_LineNumber;
    procedure TestOPDF_MainScope_RecType;
    procedure TestOPDF_MainScope_LowPC;
    procedure TestOPDF_MainScope_LineInfo;
    { Step 6c }
    procedure TestOPDF_Pointer_RecType;
    procedure TestOPDF_Array_Static_RecType;
    procedure TestOPDF_Array_Static_IsDynamic;
    procedure TestOPDF_Array_MultiDim_EmitsNestedRecords;
    procedure TestOPDF_Array_OpenArray_ArrayKind;
    procedure TestOPDF_OpenArray_CompanionLocation;
    procedure TestOPDF_Set_RecType;
    procedure TestOPDF_Set_SizeInBytes;
    procedure TestOPDF_Property_RecType;
    procedure TestOPDF_Property_MethodBacked_LayoutIntact;
    procedure TestOPDF_Interface_RecType;
    procedure TestOPDF_Constant_OrdRecord;
    procedure TestOPDF_Constant_OrdValue;
    procedure TestOPDF_Constant_StrRecord;
    procedure TestOPDF_Constant_BooleanTyped;
    procedure TestOPDF_Constant_Real;
    procedure TestOPDF_UnitDir_Present;
    procedure TestOPDF_UnitDir_UnitCount;
    { recRuntimeHelper — RTL release routines the debugger injects to free a
      +1 transient an injected property getter returns. }
    procedure TestOPDF_RuntimeHelper_StringRelease;
    procedure TestOPDF_RuntimeHelper_DynArrayRelease;
    procedure TestOPDF_RuntimeHelper_KindOrdinals;
  end;

implementation

function TOPDFTests.GenOPDF(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  E:  TOPDFEmitter;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    E := TOPDFEmitter.Create(Pr, 'test.pas');
    try
      Result := E.GetOutput();
    finally
      E.Free();
    end;
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TOPDFTests.Contains(const AText, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AText) > 0;
end;

{ ------------------------------------------------------------------ }

procedure TOPDFTests.TestOPDF_SectionDeclaration;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('section directive present', Contains(IR, '.section .opdf'));
end;

procedure TOPDFTests.TestOPDF_HeaderMagic;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('OPDF magic bytes present', Contains(IR, '.byte 79, 80, 68, 70'));
end;

procedure TOPDFTests.TestOPDF_HeaderVersion;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('version word present', Contains(IR, '.2byte 1'));
end;

procedure TOPDFTests.TestOPDF_TotalRecordsStreamTerminated;
var
  IR: string;
begin
  { Stream-terminated mode: TotalRecords stays 0 so per-unit .opdf sections
    concatenate at link time (the reader reads to section EOF, skipping any
    further 'OPDF' magic headers).  pdr ignores the count entirely. }
  IR := GenOPDF('program P; var X: Integer; begin end.');
  AssertTrue('TotalRecords is the stream-terminated zero',
    Contains(IR, '.4byte 0                        # TotalRecords (0 = stream-terminated)'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Integer;
var
  IR: string;
begin
  IR := GenOPDF('program P; var X: Integer; begin end.');
  AssertTrue('recPrimitive Integer comment', Contains(IR, '# recPrimitive: Integer'));
  AssertTrue('Integer name emitted', Contains(IR, '.ascii "Integer"'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Boolean;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recPrimitive Boolean present', Contains(IR, '# recPrimitive: Boolean'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Int64;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recPrimitive Int64 present', Contains(IR, '# recPrimitive: Int64'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Double_SubKindFloat;
{ Regression: float types emitted NO recPrimitive at all, so a Double/Single
  variable referenced a TypeID with no type record and pdr could not print it
  (locals/print/gl all failed for floats).  A Double must now emit a recPrimitive
  with SubKind=SK_FLOAT(4) and SizeInBytes=8 so pdr's TFloatEvaluator
  (Category=tcFloat, keyed off SubKind in [skFloat, skCurrency]) renders it. }
var
  IR: string;
  P:  Integer;
begin
  IR := GenOPDF('program P; var D: Double; begin D := 1.5 end.');
  AssertTrue('recPrimitive Double comment', Contains(IR, '# recPrimitive: Double'));
  AssertTrue('Double name emitted', Contains(IR, '.ascii "Double"'));
  P := Pos('# recPrimitive: Double', IR);
  AssertTrue('Double recPrimitive present', P >= 0);
  { SubKind must be SK_FLOAT (4) and size 8, in the Double record's payload. }
  AssertTrue('Double SubKind = 4 (skFloat)',
    Pos('.byte 4  # SubKind', Copy(IR, P, 220)) >= 0);
  AssertTrue('Double SizeInBytes = 8',
    Pos('.byte 8  # SizeInBytes', Copy(IR, P, 220)) >= 0);
end;

procedure TOPDFTests.TestOPDF_Primitive_Single_SubKindFloat;
{ Single is the 4-byte float counterpart; same recPrimitive shape, size 4. }
var
  IR: string;
  P:  Integer;
begin
  IR := GenOPDF('program P; var S: Single; begin S := 1.5 end.');
  AssertTrue('recPrimitive Single comment', Contains(IR, '# recPrimitive: Single'));
  P := Pos('# recPrimitive: Single', IR);
  AssertTrue('Single recPrimitive present', P >= 0);
  AssertTrue('Single SubKind = 4 (skFloat)',
    Pos('.byte 4  # SubKind', Copy(IR, P, 220)) >= 0);
  AssertTrue('Single SizeInBytes = 4',
    Pos('.byte 4  # SizeInBytes', Copy(IR, P, 220)) >= 0);
end;

procedure TOPDFTests.TestOPDF_AnsiStr_Record;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recUtf8Str present', Contains(IR, '# recUtf8Str'));
  AssertTrue('Utf8String name emitted', Contains(IR, '.ascii "Utf8String"'));
end;

procedure TOPDFTests.TestOPDF_StringConst_SpecialChars_Escaped;
var
  IR: string;
begin
  { A string const whose value is a single double-quote must be emitted as
    `.ascii "\""`, NOT `.ascii """` (which closes the literal after the first
    quote and leaves `"  # Value` as a stray token). }
  IR := GenOPDF(
    '''
        program P;
        const Q = '"';
        begin end.
        ''');
  AssertTrue('quote value is escaped', Contains(IR, '.ascii "\""  # Value'));
  AssertFalse('no unescaped triple-quote', Contains(IR, '.ascii """  # Value'));

  { A newline in the value must become \n, not a literal line break. }
  IR := GenOPDF(
    '''
        program P;
        const NL = 'a'#10'b';
        begin end.
        ''');
  AssertTrue('newline escaped as \n', Contains(IR, '.ascii "a\nb"  # Value'));

  { A backslash must be doubled. }
  IR := GenOPDF(
    '''
        program P;
        const BS = 'a\b';
        begin end.
        ''');
  AssertTrue('backslash doubled', Contains(IR, '.ascii "a\\b"  # Value'));
end;

procedure TOPDFTests.TestOPDF_GlobalVar_QuadLabel;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var MyVar: Integer;
        begin end.
        ''');
  AssertTrue('global var .quad label', Contains(IR, '.quad MyVar'));
end;

procedure TOPDFTests.TestOPDF_GlobalVar_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var MyVar: Integer;
        begin end.
        ''');
  AssertTrue('recGlobalVar comment', Contains(IR, '# recGlobalVar: MyVar'));
end;

procedure TOPDFTests.TestOPDF_Enum_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type TColor = (clRed, clGreen, clBlue);
        begin end.
        ''');
  AssertTrue('recEnum comment', Contains(IR, '# recEnum: TColor'));
end;

procedure TOPDFTests.TestOPDF_Enum_MemberName;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type TColor = (clRed, clGreen, clBlue);
        begin end.
        ''');
  AssertTrue('enum member name in output', Contains(IR, '.ascii "clRed"'));
  AssertTrue('second member', Contains(IR, '.ascii "clBlue"'));
end;

procedure TOPDFTests.TestOPDF_Class_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type
          TDog = class
            FName: string;
          end;
        begin end.
        ''');
  AssertTrue('recClass comment', Contains(IR, '# recClass: TDog'));
end;

procedure TOPDFTests.TestOPDF_Class_VtableRef;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type
          TDog = class
            FName: string;
          end;
        begin end.
        ''');
  AssertTrue('vtable reference in class record', Contains(IR, 'vtable_TDog'));
end;

procedure TOPDFTests.TestOPDF_FunctionScope_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Greet;
        begin end;
        begin end.
        ''');
  AssertTrue('recFunctionScope comment', Contains(IR, '# recFunctionScope: Greet'));
end;

procedure TOPDFTests.TestOPDF_FunctionScope_LowPC;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Greet;
        begin end;
        begin end.
        ''');
  AssertTrue('LowPC label reference', Contains(IR, '.quad Greet'));
end;

procedure TOPDFTests.TestOPDF_Parameter_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Greet(Name: string);
        begin end;
        begin end.
        ''');
  AssertTrue('recParameter comment', Contains(IR, '# recParameter: Name'));
end;

procedure TOPDFTests.TestOPDF_LocalVar_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Compute;
        var Total: Integer;
        begin end;
        begin end.
        ''');
  AssertTrue('recLocalVar comment', Contains(IR, '# recLocalVar: Total'));
end;

procedure TOPDFTests.TestOPDF_LocalVar_RBPOffset;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Compute;
        var Total: Integer;
        begin end;
        begin end.
        ''');
  AssertTrue('RBP offset line present', Contains(IR, '# LocationData (RBP offset)'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Work;
        var X: Integer;
        begin
          X := 1;
        end;
        begin end.
        ''');
  AssertTrue('recLineInfo record present', Contains(IR, '# recLineInfo'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_FileName;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Work;
        var X: Integer;
        begin
          X := 1;
        end;
        begin end.
        ''');
  AssertTrue('source filename in line info', Contains(IR, '.ascii "test.pas"'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_LineNumber;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        procedure Work;
        var X: Integer;
        begin
          X := 1;
        end;
        begin end.
        ''');
  AssertTrue('line 5 recorded', Contains(IR, '.4byte 5  # LineNumber'));
end;

procedure TOPDFTests.TestOPDF_MainScope_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var X: Integer;
        begin
          X := 1;
        end.
        ''');
  AssertTrue('recFunctionScope for main', Contains(IR, '# recFunctionScope: P'));
end;

procedure TOPDFTests.TestOPDF_MainScope_LowPC;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var X: Integer;
        begin
          X := 1;
        end.
        ''');
  AssertTrue('main LowPC label', Contains(IR, '.quad main'));
end;

procedure TOPDFTests.TestOPDF_MainScope_LineInfo;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var X: Integer;
        begin
          X := 1;
        end.
        ''');
  AssertTrue('line 4 in main body recorded', Contains(IR, '.4byte 4  # LineNumber'));
end;

procedure TOPDFTests.TestOPDF_Pointer_RecType;
var
  IR: string;
begin
  { Use ^Integer as a class field type — inline pointer types work
    in field/var positions even though 'type T = ^Foo' in the type
    section is not yet parsed }
  IR := GenOPDF(
    '''
        program P;
        type TFoo = class
          FNext: ^Integer;
        end;
        begin end.
        ''');
  AssertTrue('recPointer comment', Contains(IR, '# recPointer: ^Integer'));
end;

procedure TOPDFTests.TestOPDF_Array_Static_RecType;
var
  IR: string;
begin
  { Inline array type in global var — type section array decls not yet parsed }
  IR := GenOPDF(
    '''
        program P;
        var A: array[1..5] of Integer;
        begin end.
        ''');
  AssertTrue('recArray comment',
    Contains(IR, '# recArray (static): array[1..5] of Integer'));
end;

procedure TOPDFTests.TestOPDF_Array_Static_IsDynamic;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        var A: array[1..5] of Integer;
        begin end.
        ''');
  AssertTrue('IsDynamic=0 for static array', Contains(IR, '.byte 0  # IsDynamic'));
end;

procedure TOPDFTests.TestOPDF_Array_MultiDim_EmitsNestedRecords;
var
  IR: string;
begin
  { A multi-dimensional array is represented as nested single-dimension
    arrays, so the OPDF emitter produces one recArray per dimension: the
    outer array[0..1] whose element is the inner array[0..2], and the inner
    array itself.  The debugger follows the element chain to reconstruct the
    full multi-dimensional structure. }
  IR := GenOPDF(
    '''
        program P;
        var A: array[0..1, 0..2] of Integer;
        begin end.
        ''');
  AssertTrue('outer recArray emitted',
    Contains(IR, '# recArray (static): array[0..1] of array[0..2] of Integer'));
  AssertTrue('inner recArray emitted',
    Contains(IR, '# recArray (static): array[0..2] of Integer'));
end;

procedure TOPDFTests.TestOPDF_Array_OpenArray_ArrayKind;
var
  IR: string;
begin
  { An open-array parameter is neither static nor dynamic: it is a (ptr, high)
    pair with no heap header.  Its recArray must carry ArrayKind=2, NOT
    IsDynamic=1 (which would make the debugger read length from data-4). }
  IR := GenOPDF(
    '''
        program P;
        procedure Bar(a: array of Integer);
        begin end;
        begin end.
        ''');
  AssertTrue('ArrayKind=2 for open array', Contains(IR, '.byte 2  # ArrayKind'));
  AssertTrue('open array is not flagged dynamic',
    not Contains(IR, 'array of Integer' + #10 + '    .byte 1  # ArrayKind'));
end;

procedure TOPDFTests.TestOPDF_OpenArray_CompanionLocation;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  E:  TOPDFEmitter;
  Facts: TDbgFacts;
  O: string;
begin
  L  := TLexer.Create('program P; begin end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  Facts := BuildSampleFacts();
  try
    A.Analyse(Pr);
    E := TOPDFEmitter.Create(Pr, 'test.pas');
    try
      E.SetFacts(Facts);
      O := E.GetOutput();
    finally
      E.Free();
    end;
    { The open-array local 'Oa' must use LocationExpr=5 (open-array) and carry
      both its data-slot offset (-32) and the companion _high offset (-40). }
    AssertTrue('open-array LocationExpr=5',
      Pos('.byte 5  # LocationExpr (open-array)', O) > 0);
    AssertTrue('open-array data offset -32',
      Pos('.2byte -32  # LocationData', O) > 0);
    AssertTrue('open-array companion _high offset -40',
      Pos('.2byte -40  # CompanionData (_high RBP offset)', O) > 0);
  finally
    Facts.Free();
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TOPDFTests.TestOPDF_Set_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type
          TDays = (Mon, Tue, Wed);
          TDaySet = set of TDays;
        var S: TDaySet;
        begin end.
        ''');
  AssertTrue('recSet comment', Contains(IR, '# recSet: TDaySet'));
end;

procedure TOPDFTests.TestOPDF_Set_SizeInBytes;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type
          TDays = (Mon, Tue, Wed);
          TDaySet = set of TDays;
        var S: TDaySet;
        begin end.
        ''');
  AssertTrue('SizeInBytes=4 for small set', Contains(IR, '.byte 4  # SizeInBytes'));
end;

procedure TOPDFTests.TestOPDF_Property_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type TFoo = class
          FVal: Integer;
          property Val: Integer read FVal write FVal;
        end;
        begin end.
        ''');
  AssertTrue('recProperty comment', Contains(IR, '# recProperty: Val'));
end;

procedure TOPDFTests.TestOPDF_Property_MethodBacked_LayoutIntact;
{ Regression for the recProperty corruption (bugs.txt, opdebugger #10/#13 era):
  a method-backed property must emit a COMPLETE, correctly-sized recProperty so
  the reader (which reads SizeOf(TDefProperty)=32 fixed bytes then the three
  length-prefixed strings) does not overshoot into the next record.  The fixed
  payload is 32 bytes (4 ClassTypeID + 4 PropTypeID + 1 ReadType + 1 WriteType +
  8 ReadAddr + 8 WriteAddr + 2+2+2 length words); RecSize = 32 + len(getterSym) +
  len(setterSym) + len(name).  For TGadget.Val read GetVal write SetVal:
  getterSym = "TGadget_GetVal" (14), setterSym = "TGadget_SetVal" (14),
  name = "Val" (3) -> RecSize = 32 + 14 + 14 + 3 = 63. }
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type TGadget = class
          FVal: Integer;
          function GetVal: Integer;
          procedure SetVal(AValue: Integer);
          property Val: Integer read GetVal write SetVal;
        end;
        function TGadget.GetVal: Integer;
        begin Result := FVal; end;
        procedure TGadget.SetVal(AValue: Integer);
        begin FVal := AValue; end;
        begin end.
        ''');
  AssertTrue('recProperty comment', Contains(IR, '# recProperty: Val'));
  { RecSize must match the fixed payload (32) + the three string lengths. }
  AssertTrue('recProperty RecSize is 63', Contains(IR, '.4byte 63  # RecSize'));
  { The getter/setter symbol names and the property name must be present as the
    three trailing strings (the fields the corruption garbled). }
  AssertTrue('getter method symbol string', Contains(IR, '.ascii "TGadget_GetVal"'));
  AssertTrue('setter method symbol string', Contains(IR, '.ascii "TGadget_SetVal"'));
  { The length words must match the actual symbol lengths. }
  AssertTrue('ReadMethodNameLen = 14', Contains(IR, '.2byte 14  # ReadMethodNameLen'));
  AssertTrue('WriteMethodNameLen = 14', Contains(IR, '.2byte 14  # WriteMethodNameLen'));
  AssertTrue('NameLen = 3', Contains(IR, '.2byte 3  # NameLen'));
end;

procedure TOPDFTests.TestOPDF_Interface_RecType;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        type IGreeter = interface
          procedure Greet;
        end;
        begin end.
        ''');
  AssertTrue('recInterface comment', Contains(IR, '# recInterface: IGreeter'));
end;

procedure TOPDFTests.TestOPDF_Constant_OrdRecord;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        const MaxVal = 100;
        begin end.
        ''');
  AssertTrue('recConstant for integer', Contains(IR, '# recConstant: MaxVal'));
end;

procedure TOPDFTests.TestOPDF_Constant_OrdValue;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        const MaxVal = 100;
        begin end.
        ''');
  AssertTrue('constant value embedded', Contains(IR, '.quad 100  # Value'));
end;

procedure TOPDFTests.TestOPDF_Constant_StrRecord;
var
  IR: string;
begin
  IR := GenOPDF(
    '''
        program P;
        const Greeting = 'Hello';
        begin end.
        ''');
  AssertTrue('recConstant for string', Contains(IR, '# recConstant: Greeting'));
end;

procedure TOPDFTests.TestOPDF_Constant_BooleanTyped;
var
  IR: string;
begin
  { A Boolean const (True/False) must emit as an ordinal (ckOrd) with value 1/0
    and a Boolean TypeID — not as an empty string constant (the pre-fix bug). }
  IR := GenOPDF(
    '''
        program P;
        const Enabled = True;
        begin end.
        ''');
  AssertTrue('recConstant for Boolean', Contains(IR, '# recConstant: Enabled'));
  AssertTrue('Boolean const is ckOrd', Contains(IR, '.byte 0  # ConstKind: ckOrd'));
  AssertTrue('Boolean const value is 1', Contains(IR, '.quad 1  # Value'));
end;

procedure TOPDFTests.TestOPDF_Constant_Real;
var
  IR: string;
begin
  { A real const must emit as ckReal with the IEEE-754 Double via .double —
    not as an all-zero ordinal (the pre-fix bug). }
  IR := GenOPDF(
    '''
        program P;
        const PiApprox = 3.14159;
        begin end.
        ''');
  AssertTrue('recConstant for real', Contains(IR, '# recConstant: PiApprox'));
  AssertTrue('real const is ckReal', Contains(IR, '.byte 2  # ConstKind: ckReal'));
  AssertTrue('real const emits .double', Contains(IR, '.double 3.14159  # Value'));
end;

procedure TOPDFTests.TestOPDF_UnitDir_Present;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recUnitDirectory present', Contains(IR, '# recUnitDirectory'));
end;

procedure TOPDFTests.TestOPDF_UnitDir_UnitCount;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('unit count is 1', Contains(IR, '.4byte 1  # UnitCount'));
end;

procedure TOPDFTests.TestOPDF_RuntimeHelper_StringRelease;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recRuntimeHelper comment for _StringRelease',
    Contains(IR, '# recRuntimeHelper: _StringRelease'));
  AssertTrue('_StringRelease address quad (linker-resolved)',
    Contains(IR, '.quad _StringRelease  # Address (linker-resolved)'));
end;

procedure TOPDFTests.TestOPDF_RuntimeHelper_DynArrayRelease;
var
  IR: string;
begin
  IR := GenOPDF('program P; begin end.');
  AssertTrue('recRuntimeHelper comment for _DynArrayRelease',
    Contains(IR, '# recRuntimeHelper: _DynArrayRelease'));
  AssertTrue('_DynArrayRelease address quad (linker-resolved)',
    Contains(IR, '.quad _DynArrayRelease  # Address (linker-resolved)'));
end;

procedure TOPDFTests.TestOPDF_RuntimeHelper_KindOrdinals;
var
  IR: string;
begin
  { Kind ordinals must match opdf_types.TRuntimeHelperKind: string=0, dynarray=1 }
  IR := GenOPDF('program P; begin end.');
  AssertTrue('rhkStringRelease kind byte = 0', Contains(IR, '.byte 0  # Kind'));
  AssertTrue('rhkDynArrayRelease kind byte = 1', Contains(IR, '.byte 1  # Kind'));
end;

procedure TOPDFTests.TestOPDF_MethodScope_Emitted;
var O: string;
begin
  O := GenOPDF('''
      program P;
      type
        TThing = class
          N: Integer;
          procedure Bump();
        end;
      procedure TThing.Bump();
      begin
        N := N + 1;
      end;
      var T: TThing;
      begin
        T := TThing.Create();
        T.Bump();
      end.
      ''');
  AssertTrue('method gets a function scope record',
    Pos('recFunctionScope: TThing_Bump', O) > 0);
end;

procedure TOPDFTests.TestOPDF_DestructorScope_Emitted;
var O: string;
begin
  O := GenOPDF('''
      program P;
      type
        TThing = class
          N: Integer;
          destructor Destroy();
        end;
      destructor TThing.Destroy();
      begin
        N := 0;
      end;
      var T: TThing;
      begin
        T := TThing.Create();
        T.Free();
      end.
      ''');
  AssertTrue('destructor gets a function scope record',
    Pos('recFunctionScope: TThing_Destroy', O) > 0);
end;

function BuildSampleFacts: TDbgFacts;
var
  F: TDbgFunc;
  LineRec: TDbgLine;
  V: TDbgVar;
begin
  Result := TDbgFacts.Create();
  F := Result.BeginFunc('TThing_Bump');
  F.EndLabel := '.Ldbg_end_7';
  V := F.AddVar('Self', nil, -8);
  V.IsParam := True;
  V := F.AddVar('By', nil, -16);
  V.IsParam := True;
  F.AddVar('Tmp', nil, -24);
  { Open-array parameter: data slot at -32, companion _high slot at -40.
    The OPDF emitter must locate the length via the companion offset. }
  V := F.AddVar('Oa', nil, -32);
  V.IsParam := True;
  V.IsOpenArray := True;
  V.HighRbpOffset := -40;
  LineRec := TDbgLine.Create();
  LineRec.LabelName := '.Ldbg_3';
  LineRec.Line := 10;
  LineRec.Col := 3;
  F.Lines.Add(LineRec);
  LineRec := TDbgLine.Create();
  LineRec.LabelName := '.Ldbg_4';
  LineRec.Line := 11;
  LineRec.Col := 3;
  F.Lines.Add(LineRec);
end;

procedure TOPDFTests.TestOPDF_Facts_ExactScopeAndLocals;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  E:  TOPDFEmitter;
  Facts: TDbgFacts;
  O: string;
begin
  L  := TLexer.Create('program P; begin end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  Facts := BuildSampleFacts();
  try
    A.Analyse(Pr);
    E := TOPDFEmitter.Create(Pr, 'test.pas');
    try
      E.SetFacts(Facts);
      O := E.GetOutput();
    finally
      E.Free();
    end;
    AssertTrue('scope record present', Pos('recFunctionScope: TThing_Bump', O) > 0);
    AssertTrue('exact HighPC end label', Pos('.quad .Ldbg_end_7  # HighPC', O) > 0);
    AssertTrue('param record for By', Pos('recParameter: By', O) > 0);
    AssertTrue('local with real offset', Pos('.2byte -24  # LocationData', O) > 0);
    AssertTrue('param locatable too (Self at -8)', Pos('.2byte -8  # LocationData', O) > 0);
  finally
    Facts.Free();
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TOPDFTests.TestOPDF_Facts_PerStatementLines;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  E:  TOPDFEmitter;
  Facts: TDbgFacts;
  O: string;
begin
  L  := TLexer.Create('program P; begin end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  Facts := BuildSampleFacts();
  try
    A.Analyse(Pr);
    E := TOPDFEmitter.Create(Pr, 'test.pas');
    try
      E.SetFacts(Facts);
      O := E.GetOutput();
    finally
      E.Free();
    end;
    AssertTrue('line 10 record uses statement label',
      Pos('.quad .Ldbg_3  # Address (statement label)', O) > 0);
    AssertTrue('line 11 record uses statement label',
      Pos('.quad .Ldbg_4  # Address (statement label)', O) > 0);
  finally
    Facts.Free();
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

initialization
  RegisterTest(TOPDFTests);

end.
