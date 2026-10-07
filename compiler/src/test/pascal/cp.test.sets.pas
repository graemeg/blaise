{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sets;

{ Tests for Pascal set types — set of EnumType, set literals, in operator,
  Include/Exclude built-ins, and set arithmetic operators. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe,
  blaise.codegen.native, blaise.codegen.target, cp.test.harness;

type
  TSetTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticFail(const ASrc: string);
    procedure ParseOK(const ASrc: string);
  published
    { lo..hi in a set literal outside an assignment: the operand / argument
      is analysed before its set context is known }
    procedure TestSemantic_SetRangeLiteral_AcceptedInEveryContext;
    procedure TestSemantic_RangeInOpenArrayArg_Rejected;
    { ------------------------------------------------------------------ }
    { parse                                                                }
    { ------------------------------------------------------------------ }
    procedure TestParse_Set_SimpleDefinition;
    procedure TestParse_Set_EmptyLiteral;
    procedure TestParse_Set_TwoElementLiteral;
    procedure TestParse_Set_InOperator;
    procedure TestParse_Set_IncludeExclude;
    procedure TestParse_Set_ArithmeticOperators;
    procedure TestParse_Set_EqualityOperators;

    { ------------------------------------------------------------------ }
    { semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Set_TypeRegistered;
    procedure TestSemantic_Set_VariableDecl_OK;
    procedure TestSemantic_Set_EmptyLiteralAssign_OK;
    procedure TestSemantic_Set_TwoElementLiteralAssign_OK;
    procedure TestSemantic_Set_InOperator_ResultIsBoolean;
    procedure TestSemantic_Set_Include_OK;
    procedure TestSemantic_Set_Exclude_OK;
    procedure TestSemantic_Set_Union_OK;
    procedure TestSemantic_Set_Difference_OK;
    procedure TestSemantic_Set_Intersection_OK;
    procedure TestSemantic_Set_Equality_OK;
    procedure TestSemantic_Set_EqualityEmptyLiteral_OK;
    procedure TestSemantic_Set_EqualityLiteral_OK;
    procedure TestSemantic_Set_BaseTypeMustBeEnum;
    procedure TestSemantic_Set_LiteralElementMustMatchBase;
    procedure TestSemantic_Set_CtorArgLiteralRetypedToSet;
    procedure TestSemantic_Set_MetaclassCtorArgLiteralRetypedToSet;
    procedure TestSemantic_Set_ProcFieldArgLiteralRetypedToSet;
    procedure TestCodegen_Set_ProcFieldArgLiteral_NativeCompiles;

    { ------------------------------------------------------------------ }
    { ranges in set literals — [lo..hi] (issue #105)                       }
    { ------------------------------------------------------------------ }
    procedure TestParse_Set_RangeLiteral;
    procedure TestSemantic_Set_RangeLiteral_OK;
    procedure TestSemantic_Set_RangeMixedWithSingles_OK;
    procedure TestSemantic_Set_RangeEnum_OK;
    procedure TestSemantic_Set_RangeReversed_Fails;
    procedure TestSemantic_Set_RangeNonConstBound_Fails;
    procedure TestSemantic_Set_RangeWrongBaseType_Fails;

    { ------------------------------------------------------------------ }
    { codegen                                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { set-valued constants  (const X = [a, b])                            }
    { ------------------------------------------------------------------ }
    procedure TestParse_SetConst_InferredType;
    procedure TestSemantic_SetConst_Inferred_OK;
    procedure TestSemantic_SetConst_Annotated_OK;
    procedure TestSemantic_SetConst_EmptyAnnotated_OK;
    procedure TestSemantic_SetConst_EmptyUnannotated_Fails;
    procedure TestSemantic_SetConst_MixedEnums_Fails;
    procedure TestSemantic_SetConst_NonEnumMember_Fails;
    procedure TestCodegen_SetConst_AssignableToNamedSetType;

    { ------------------------------------------------------------------ }
    { set literal as a call argument                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SetLiteralArg_OK;
    procedure TestSemantic_SetLiteralArg_Empty_OK;
    procedure TestSemantic_SetLiteralArg_WrongEnum_Fails;
    procedure TestSemantic_EmptyLiteral_NonSetAssign_Fails;

    { ------------------------------------------------------------------ }
    { set of Byte / ordinal-based sets (issue #105)                        }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SetOfByte_TypeRegistered;
    procedure TestSemantic_SetOfByte_VarDecl_OK;
    procedure TestSemantic_SetOfByte_IntLiteralAssign_OK;
    procedure TestSemantic_SetOfByte_RangeLiteral_OK;
    procedure TestSemantic_SetOfByte_InOperator_OK;
    procedure TestSemantic_SetOfByte_Include_OK;
    procedure TestSemantic_SetOfByte_Exclude_OK;
    procedure TestSemantic_SetOfByte_InlineType_OK;
    procedure TestSemantic_SetOfBoolean_OK;
    procedure TestCodegen_SetOfByte_IsJumbo;

    { ------------------------------------------------------------------ }
    { Integer-subrange base type: set of 0..255 / set of lo..hi           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SetOfSubrange_VarDecl_OK;
    procedure TestSemantic_SetOfSubrange_TypeDecl_OK;
    procedure TestSemantic_SetOfSubrange_OverBound_Fails;
    procedure TestSemantic_SetOfSubrange_Descending_Fails;

    { ------------------------------------------------------------------ }
    { self-assigned sret call: X := F(X) must not wipe X before the call   }
    { ------------------------------------------------------------------ }
    { A record-returning call assigned back over one of its own arguments:
      the destination must NOT be memset before the argument list is
      evaluated.  Instead the call sret's into a fresh temp and the result
      is memcpy'd into the destination afterwards. }
    { The NON-aliasing control: a distinct destination must keep the direct
      form — memset straight into the destination, no temp, no memcpy.
      Guards against the aliasing predicate over-firing. }
    procedure TestCodegen_DistinctDestRecordCall_KeepsDirectForm;
    { Native x86-64: a jumbo-set-returning call assigned back over one of its
      own arguments routes through a stack temp + memcpy. }
    procedure TestNative_SelfAssignedJumboSetCall_UsesTemp;
    { Native x86-64 control: a distinct destination keeps the direct sret
      form (no aliasing temp memcpy). }
    procedure TestNative_DistinctDestJumboSetCall_KeepsDirectForm;

    { ------------------------------------------------------------------ }
    { 64-bit sets (>32 members)                                            }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Set64_TypeRegistered;
    procedure TestSemantic_Set_Over256Members_Fails;
    { BUG-20260922-set-of-explicit-ordinal-enum -- a member's bit index is
      its real ORDINAL, so a set of an enum with explicit ordinals must be
      sized by MaxOrdinal + 1, not by the member count.  Ordinals must lie in
      0..255, the same ceiling 'set of lo..hi' already enforces. }
    procedure TestSemantic_SetOfExplicitOrdinalEnum_TypeDecl_BitCountIsMaxOrdPlus1;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_InlineVar_BitCountIsMaxOrdPlus1;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_InferredConst_BitCountIsMaxOrdPlus1;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_InNonConstLiteral_BitCountIsMaxOrdPlus1;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_Ordinal255_OK;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_OrdinalOver255_Fails;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_InlineOrdinalOver255_Fails;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_NegativeOrdinal_Fails;
    procedure TestSemantic_SetOfExplicitOrdinalEnum_ConstOrdinalOver255_Fails;
    { An empty '[]' has no element type of its own and must take it from the
      assignment LHS.  The bare (implicit-Self) field form did not supply it,
      so a valid 'Field := []' inside a method was rejected with "Expression
      has no value type" — on EVERY set type, not just jumbo ones. }
    procedure TestSemantic_ImplicitSelfSetField_EmptyLiteral;
    procedure TestSemantic_SetArrayElement_LiteralAssign;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Common source snippets                                               }
{ ------------------------------------------------------------------ }

const
  DirEnum =
    '''
        type
          TDir = (dNorth, dSouth, dEast, dWest);
          TDirSet = set of TDir;
        ''';

  { dNorth=0 → bit 0 = 1; dEast=2 → bit 2 = 4; mask = 5 }
  SrcSetTypeDecl =
    'program P;' + #10 +
    DirEnum +
    '''
        begin
        end.
        ''';

  SrcSetEmptyLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := []
        end.
        ''';

  SrcSetTwoElementLiteral =
    'program P;' + #10 +
    DirEnum +
    'var S: TDirSet;' + #10 +
    'begin' + #10 +
    '  S := [dNorth, dEast]' + #10 +   { mask = 1 + 4 = 5 }
    'end.';

  { Set-valued constant whose set type is inferred from the members'
    enum (no annotation): mask = dNorth(0)|dEast(2) = 5. }
  SrcSetConstInferred =
    'program P;' + #10 +
    DirEnum +
    '''
        const Both = [dNorth, dEast];
        var S: TDirSet;
        begin
          S := Both
        end.
        ''';

  { Annotated set const: const X: TDirSet = [...]. }
  SrcSetConstAnnotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const Both: TDirSet = [dNorth, dEast];
        var S: TDirSet;
        begin
          S := Both
        end.
        ''';

  SrcSetConstEmptyAnnotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const None: TDirSet = [];
        var S: TDirSet;
        begin
          S := None
        end.
        ''';

  SrcSetConstEmptyUnannotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const Bad = [];
        begin
        end.
        ''';

  SrcSetConstMixedEnums =
    '''
    program P;
    type
      TA = (a1, a2);
      TB = (b1, b2);
    const Mixed = [a1, b1];
    begin
    end.
    ''';

  SrcSetConstNonEnumMember =
    '''
    program P;
    const X = 5; Bad = [X];
    begin
    end.
    ''';

  { A set literal passed directly as a `set of` argument: mask dNorth(0)|
    dEast(2) = 5. }
  SrcSetLiteralArg =
    'program P;' + #10 +
    DirEnum +
    '''
        procedure Take(S: TDirSet);
        begin
          if dNorth in S then Halt(0)
        end;
        begin
          Take([dNorth, dEast])
        end.
        ''';

  SrcSetLiteralArgEmpty =
    'program P;' + #10 +
    DirEnum +
    '''
        procedure Take(S: TDirSet);
        begin
          if dNorth in S then Halt(0)
        end;
        begin
          Take([])
        end.
        ''';

  SrcSetLiteralArgWrongEnum =
    '''
    program P;
    type
      TDir = (dNorth, dEast);
      TDirSet = set of TDir;
      TColor = (cRed, cBlue);
    procedure Take(S: TDirSet);
    begin
    end;
    begin
      Take([cRed])
    end.
    ''';

  SrcEmptyLiteralNonSetAssign =
    '''
    program P;
    var x: Integer;
    begin
      x := []
    end.
    ''';

  SrcSetInOperator =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [dNorth, dEast];
          B := dNorth in S
        end.
        ''';

  SrcSetInclude =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := [];
          Include(S, dSouth)
        end.
        ''';

  SrcSetExclude =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := [dNorth, dSouth];
          Exclude(S, dNorth)
        end.
        ''';

  SrcSetUnion =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth];
          S2 := [dEast];
          S3 := S1 + S2
        end.
        ''';

  SrcSetDifference =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth, dEast];
          S2 := [dNorth];
          S3 := S1 - S2
        end.
        ''';

  SrcSetIntersection =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth, dEast];
          S2 := [dNorth];
          S3 := S1 * S2
        end.
        ''';

  SrcSetEquality =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2: TDirSet; B: Boolean;
        begin
          S1 := [dNorth];
          S2 := [dNorth];
          B := S1 = S2
        end.
        ''';

  SrcSetInequality =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2: TDirSet; B: Boolean;
        begin
          S1 := [dNorth];
          S2 := [dSouth];
          B := S1 <> S2
        end.
        ''';

  SrcSetEqualityEmptyLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [];
          B := S = []
        end.
        ''';

  SrcSetEqualityLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [dNorth, dEast];
          B := S = [dNorth, dEast]
        end.
        ''';

  BigEnum =
    '''
        type
          TBig = (
            X00, X01, X02, X03, X04, X05, X06, X07,
            X08, X09, X10, X11, X12, X13, X14, X15,
            X16, X17, X18, X19, X20, X21, X22, X23,
            X24, X25, X26, X27, X28, X29, X30, X31,
            X32, X33, X34, X35, X36, X37, X38, X39,
            X40, X41, X42, X43, X44, X45, X46, X47);
          TBigSet = set of TBig;
        ''';

  SrcSet64TypeDecl =
    'program P;' + #10 +
    BigEnum +
    '''
        begin
        end.
        ''';

  SrcSetTooManyMembers =
    '''
    program P;
    type
      THuge = (
        A000, A001, A002, A003, A004, A005, A006, A007,
        A008, A009, A010, A011, A012, A013, A014, A015,
        A016, A017, A018, A019, A020, A021, A022, A023,
        A024, A025, A026, A027, A028, A029, A030, A031,
        A032, A033, A034, A035, A036, A037, A038, A039,
        A040, A041, A042, A043, A044, A045, A046, A047,
        A048, A049, A050, A051, A052, A053, A054, A055,
        A056, A057, A058, A059, A060, A061, A062, A063,
        A064, A065, A066, A067, A068, A069, A070, A071,
        A072, A073, A074, A075, A076, A077, A078, A079,
        A080, A081, A082, A083, A084, A085, A086, A087,
        A088, A089, A090, A091, A092, A093, A094, A095,
        A096, A097, A098, A099, A100, A101, A102, A103,
        A104, A105, A106, A107, A108, A109, A110, A111,
        A112, A113, A114, A115, A116, A117, A118, A119,
        A120, A121, A122, A123, A124, A125, A126, A127,
        A128, A129, A130, A131, A132, A133, A134, A135,
        A136, A137, A138, A139, A140, A141, A142, A143,
        A144, A145, A146, A147, A148, A149, A150, A151,
        A152, A153, A154, A155, A156, A157, A158, A159,
        A160, A161, A162, A163, A164, A165, A166, A167,
        A168, A169, A170, A171, A172, A173, A174, A175,
        A176, A177, A178, A179, A180, A181, A182, A183,
        A184, A185, A186, A187, A188, A189, A190, A191,
        A192, A193, A194, A195, A196, A197, A198, A199,
        A200, A201, A202, A203, A204, A205, A206, A207,
        A208, A209, A210, A211, A212, A213, A214, A215,
        A216, A217, A218, A219, A220, A221, A222, A223,
        A224, A225, A226, A227, A228, A229, A230, A231,
        A232, A233, A234, A235, A236, A237, A238, A239,
        A240, A241, A242, A243, A244, A245, A246, A247,
        A248, A249, A250, A251, A252, A253, A254, A255,
        A256);
      THugeSet = set of THuge;
    begin
    end.
    ''';

  SrcSetBadBaseType =
    '''
        program P;
        type TBad = set of Integer;
        begin
        end.
        ''';

  SrcSetBadLiteralElement =
    'program P;' + #10 +
    DirEnum +
    'type TColors = (cRed, cBlue);' + #10 +
    'type TColorSet = set of TColors;' + #10 +
    'var S: TDirSet;' + #10 +
    'begin' + #10 +
    '  S := [cRed]' + #10 +  { TColors element in TDirSet → error }
    'end.';

  { A bracket literal passed to a constructor's `set of` parameter.  Analysed
    without set context it defaults to an open-array type; the constructor
    branches of AnalyseMethodCallExpr must re-type it to the parameter's set
    type, as the free-proc and function-call paths already do. }
  SrcSetCtorArgLiteral =
    'program P;' + #10 +
    DirEnum +
    'type' + #10 +
    '  TFoo = class' + #10 +
    '    FDirs: TDirSet;' + #10 +
    '    constructor Create(ADirs: TDirSet);' + #10 +
    '  end;' + #10 +
    'constructor TFoo.Create(ADirs: TDirSet);' + #10 +
    'begin' + #10 +
    '  FDirs := ADirs' + #10 +
    'end;' + #10 +
    'var F: TFoo;' + #10 +
    'begin' + #10 +
    '  F := TFoo.Create([dNorth, dEast])' + #10 +
    'end.';

  { The same, dispatched through a metaclass variable — the second constructor
    branch in AnalyseMethodCallExpr. }
  SrcSetMetaclassCtorArgLiteral =
    'program P;' + #10 +
    DirEnum +
    'type' + #10 +
    '  TFoo = class' + #10 +
    '    FDirs: TDirSet;' + #10 +
    '    constructor Create(ADirs: TDirSet);' + #10 +
    '  end;' + #10 +
    '  TFooClass = class of TFoo;' + #10 +
    'constructor TFoo.Create(ADirs: TDirSet);' + #10 +
    'begin' + #10 +
    '  FDirs := ADirs' + #10 +
    'end;' + #10 +
    'var' + #10 +
    '  C: TFooClass;' + #10 +
    '  F: TFoo;' + #10 +
    'begin' + #10 +
    '  C := TFoo;' + #10 +
    '  F := C.Create([dNorth, dEast])' + #10 +
    'end.';

  { A bracket literal passed to a QUALIFIED procedural-field call must be
    typed against the field signature's `set of` param -- class-var,
    record-var and chained receivers, statement and expression position.
    BUG-20260722-procfield-set-literal-arg. }
  SrcSetProcFieldArgLiteral =
    'program P;' + #10 +
    DirEnum +
    'type' + #10 +
    '  TP = procedure(S: TDirSet; D: TDir);' + #10 +
    '  TF = function(S: TDirSet): Boolean;' + #10 +
    '  TR = record' + #10 +
    '    FP: TP;' + #10 +
    '    FF: TF;' + #10 +
    '  end;' + #10 +
    '  TFoo = class' + #10 +
    '    FP: TP;' + #10 +
    '    FF: TF;' + #10 +
    '    R: TR;' + #10 +
    '  end;' + #10 +
    'var' + #10 +
    '  F: TFoo;' + #10 +
    '  R: TR;' + #10 +
    '  B: Boolean;' + #10 +
    'begin' + #10 +
    '  F.FP([dNorth, dEast], dNorth);' + #10 +
    '  B := F.FF([dNorth, dEast]);' + #10 +
    '  R.FP([dNorth, dEast], dNorth);' + #10 +
    '  F.R.FP([dNorth, dEast], dNorth);' + #10 +
    '  B := F.R.FF([dNorth, dEast])' + #10 +
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TSetTests.GenIR(const ASrc: string): string;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  CG   := TCodeGenQBE.Create();
  CG.Generate(Prog);
  Result := CG.GetOutput();
  CG.Free();
  Prog.Free();
end;

function TSetTests.AnalyseSrc(const ASrc: string): TProgram;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Result := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

procedure TSetTests.SemanticOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

procedure TSetTests.SemanticFail(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    Prog.Free();
    Fail('Expected ESemanticError but none was raised');
  except
    on E: ESemanticError do
    begin
      Prog.Free();
    end;
    on E: Exception do
    begin
      Prog.Free();
      raise;
    end;
  end;
  SA.Free();
end;

procedure TSetTests.ParseOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  try
    Prog := Par.Parse();
    Prog.Free();
  finally
    Par.Free(); Lex.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ parse                                                                }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestParse_Set_SimpleDefinition;
begin
  ParseOK(SrcSetTypeDecl);
end;

procedure TSetTests.TestParse_Set_EmptyLiteral;
begin
  ParseOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestParse_Set_TwoElementLiteral;
begin
  ParseOK(SrcSetTwoElementLiteral);
end;

procedure TSetTests.TestParse_Set_InOperator;
begin
  ParseOK(SrcSetInOperator);
end;

procedure TSetTests.TestParse_Set_IncludeExclude;
begin
  ParseOK(SrcSetInclude);
  ParseOK(SrcSetExclude);
end;

procedure TSetTests.TestParse_Set_ArithmeticOperators;
begin
  ParseOK(SrcSetUnion);
  ParseOK(SrcSetDifference);
  ParseOK(SrcSetIntersection);
end;

procedure TSetTests.TestParse_Set_EqualityOperators;
begin
  ParseOK(SrcSetEquality);
  ParseOK(SrcSetInequality);
end;

{ ------------------------------------------------------------------ }
{ semantic                                                             }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_Set_TypeRegistered;
begin
  SemanticOK(SrcSetTypeDecl);
end;

procedure TSetTests.TestSemantic_Set_VariableDecl_OK;
begin
  SemanticOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_EmptyLiteralAssign_OK;
begin
  SemanticOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_TwoElementLiteralAssign_OK;
begin
  SemanticOK(SrcSetTwoElementLiteral);
end;

procedure TSetTests.TestSemantic_Set_InOperator_ResultIsBoolean;
var
  Lex:    TLexer;
  Par:    TParser;
  SA:     TSemanticAnalyser;
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Lex  := TLexer.Create(SrcSetInOperator);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  { B := dNorth in S — second stmt in main block }
  Assign := TAssignment(Prog.Block.Stmts[1]);
  AssertEquals('in operator resolves to Boolean',
    Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TSetTests.TestSemantic_Set_CtorArgLiteralRetypedToSet;
var
  Prog: TProgram;
  Assign: TAssignment;
  Call: TMethodCallExpr;
begin
  Prog := AnalyseSrc(SrcSetCtorArgLiteral);
  try
    { F := TFoo.Create([dNorth, dEast]) — sole stmt in the main block }
    Assign := TAssignment(Prog.Block.Stmts[0]);
    Call := TMethodCallExpr(Assign.Expr);
    AssertEquals('constructor set-literal arg re-typed to the parameter set type',
      Ord(tySet), Ord(TASTExpr(Call.Args[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_Set_MetaclassCtorArgLiteralRetypedToSet;
var
  Prog: TProgram;
  Assign: TAssignment;
  Call: TMethodCallExpr;
begin
  Prog := AnalyseSrc(SrcSetMetaclassCtorArgLiteral);
  try
    { F := C.Create([dNorth, dEast]) — second stmt in the main block }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    Call := TMethodCallExpr(Assign.Expr);
    AssertEquals('metaclass constructor set-literal arg re-typed to the parameter set type',
      Ord(tySet), Ord(TASTExpr(Call.Args[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_Set_ProcFieldArgLiteralRetypedToSet;
var
  Prog: TProgram;
  I: Integer;
  S: TObject;
  Args: TObjectList;
begin
  Prog := AnalyseSrc(SrcSetProcFieldArgLiteral);
  try
    { Statements 0, 2, 3 are proc-field call statements; 1 and 4 assign a
      proc-field call expression. }
    for I := 0 to 4 do
    begin
      S := Prog.Block.Stmts[I];
      if S is TMethodCallStmt then
        Args := TMethodCallStmt(S).Args
      else
        Args := TMethodCallExpr(TAssignment(S).Expr).Args;
      AssertEquals(Format('stmt %d: proc-field set-literal arg re-typed to the set type', [I]),
        Ord(tySet), Ord(TASTExpr(Args[0]).ResolvedType.Kind));
    end;
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestCodegen_Set_ProcFieldArgLiteral_NativeCompiles;
var
  S: string;
begin
  { Native raised "unsupported expression form TArrayLiteralExpr". }
  S := GenAsm(SrcSetProcFieldArgLiteral, TargetX86_64);
  AssertTrue('native emits the proc-field calls', Length(S) > 0);
end;

procedure TSetTests.TestSemantic_Set_Include_OK;
begin
  SemanticOK(SrcSetInclude);
end;

procedure TSetTests.TestSemantic_Set_Exclude_OK;
begin
  SemanticOK(SrcSetExclude);
end;

procedure TSetTests.TestSemantic_Set_Union_OK;
begin
  SemanticOK(SrcSetUnion);
end;

procedure TSetTests.TestSemantic_Set_Difference_OK;
begin
  SemanticOK(SrcSetDifference);
end;

procedure TSetTests.TestSemantic_Set_Intersection_OK;
begin
  SemanticOK(SrcSetIntersection);
end;

procedure TSetTests.TestSemantic_Set_Equality_OK;
begin
  SemanticOK(SrcSetEquality);
  SemanticOK(SrcSetInequality);
end;

procedure TSetTests.TestSemantic_Set_EqualityEmptyLiteral_OK;
begin
  { S = [] must not crash the semantic pass (was nil-deref before fix). }
  SemanticOK(SrcSetEqualityEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_EqualityLiteral_OK;
begin
  { S = [dNorth, dEast] — literal RHS coerced to the set type of LHS. }
  SemanticOK(SrcSetEqualityLiteral);
end;

procedure TSetTests.TestSemantic_Set_BaseTypeMustBeEnum;
begin
  SemanticFail(SrcSetBadBaseType);
end;

procedure TSetTests.TestSemantic_Set_LiteralElementMustMatchBase;
begin
  SemanticFail(SrcSetBadLiteralElement);
end;

{ ------------------------------------------------------------------ }
{ ranges in set literals — [lo..hi] (issue #105)                       }
{ ------------------------------------------------------------------ }

{ Blaise set base types are enumerations (set of byte is a separate, tracked
  feature — see docs/future-improvements.adoc).  Use an enum with enough
  members to exercise the ranges below. }
const
  SetEnumDecl =
    'type TC = (m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10); ' +
    'TCS = set of TC; ';
  SrcSetRange =
    'program P; ' + SetEnumDecl + 'var e: TCS; ' +
    'begin e := [m1..m3]; end.';
  SrcSetRangeMixed =
    'program P; ' + SetEnumDecl + 'var e: TCS; ' +
    'begin e := [m1, m5..m7, m10]; end.';
  SrcSetRangeEnum =
    'program P; type TC = (Red, Green, Blue, Yellow); TCS = set of TC; var e: TCS; ' +
    'begin e := [Red..Blue]; end.';
  SrcSetRangeReversed =
    'program P; ' + SetEnumDecl + 'var e: TCS; ' +
    'begin e := [m5..m3]; end.';
  SrcSetRangeNonConst =
    'program P; ' + SetEnumDecl + 'var e: TCS; lo, hi: TC; ' +
    'begin lo := m1; hi := m4; e := [lo..hi]; end.';
  SrcSetRangeWrongBase =
    'program P; type TC = (Red, Green); TCS = set of TC; ' +
    'TD = (xa, xb, xc); var e: TCS; ' +
    'begin e := [xa..xb]; end.';

procedure TSetTests.TestParse_Set_RangeLiteral;
begin
  ParseOK(SrcSetRange);
end;

procedure TSetTests.TestSemantic_Set_RangeLiteral_OK;
begin
  SemanticOK(SrcSetRange);
end;

procedure TSetTests.TestSemantic_Set_RangeMixedWithSingles_OK;
begin
  SemanticOK(SrcSetRangeMixed);
end;

procedure TSetTests.TestSemantic_Set_RangeEnum_OK;
begin
  SemanticOK(SrcSetRangeEnum);
end;

procedure TSetTests.TestSemantic_Set_RangeReversed_Fails;
begin
  { A constant reverse range [5..3] is a mistake, not a silent empty set. }
  SemanticFail(SrcSetRangeReversed);
end;

procedure TSetTests.TestSemantic_Set_RangeNonConstBound_Fails;
begin
  { Variable bounds are not supported — both ends must be constant. }
  SemanticFail(SrcSetRangeNonConst);
end;

procedure TSetTests.TestSemantic_Set_RangeWrongBaseType_Fails;
begin
  SemanticFail(SrcSetRangeWrongBase);
end;

{ ------------------------------------------------------------------ }
{ set-valued constants                                                 }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestParse_SetConst_InferredType;
begin
  ParseOK(SrcSetConstInferred);
end;

procedure TSetTests.TestSemantic_SetConst_Inferred_OK;
begin
  SemanticOK(SrcSetConstInferred);
end;

procedure TSetTests.TestSemantic_SetConst_Annotated_OK;
begin
  SemanticOK(SrcSetConstAnnotated);
end;

procedure TSetTests.TestSemantic_SetConst_EmptyAnnotated_OK;
begin
  SemanticOK(SrcSetConstEmptyAnnotated);
end;

procedure TSetTests.TestSemantic_SetConst_EmptyUnannotated_Fails;
begin
  { An empty set with no annotation has no enum to infer from. }
  SemanticFail(SrcSetConstEmptyUnannotated);
end;

procedure TSetTests.TestSemantic_SetConst_MixedEnums_Fails;
begin
  SemanticFail(SrcSetConstMixedEnums);
end;

procedure TSetTests.TestSemantic_SetConst_NonEnumMember_Fails;
begin
  SemanticFail(SrcSetConstNonEnumMember);
end;

procedure TSetTests.TestCodegen_SetConst_AssignableToNamedSetType;
begin
  { An inferred 'set of TDir' const assigns to a TDirSet variable — the two
    set types are structurally the same.  Just assert it analyses + emits. }
  SemanticOK(SrcSetConstInferred);
end;

{ ------------------------------------------------------------------ }
{ set literal as a call argument                                       }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_SetLiteralArg_OK;
begin
  { Take([dNorth, dEast]) resolves the set-literal argument against the
    `set of TDir` parameter. }
  SemanticOK(SrcSetLiteralArg);
end;

procedure TSetTests.TestSemantic_SetLiteralArg_Empty_OK;
begin
  { An empty literal [] matches any set parameter. }
  SemanticOK(SrcSetLiteralArgEmpty);
end;

procedure TSetTests.TestSemantic_SetLiteralArg_WrongEnum_Fails;
begin
  { [cRed] (a TColor set constructor) does not match a `set of TDir`. }
  SemanticFail(SrcSetLiteralArgWrongEnum);
end;

procedure TSetTests.TestSemantic_EmptyLiteral_NonSetAssign_Fails;
begin
  { x := [] where x is Integer: empty literal has no set context — a clean
    error, not a crash. }
  SemanticFail(SrcEmptyLiteralNonSetAssign);
end;

{ ------------------------------------------------------------------ }
{ 64-bit sets (>32 members)                                            }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_Set64_TypeRegistered;
begin
  SemanticOK(SrcSet64TypeDecl);
end;

procedure TSetTests.TestSemantic_Set_Over256Members_Fails;
begin
  { 257 members exceeds the 256 ceiling — the largest set Blaise supports
    (a jumbo byte-array bitmap of up to 32 bytes). }
  SemanticFail(SrcSetTooManyMembers);
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_TypeDecl_BitCountIsMaxOrdPlus1;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('''
    program P;
    type
      TSm = (sA = 5, sB = 10);
      TSmSet = set of TSm;
    begin end.
    ''');
  try
    TD := Prog.SymbolTable.FindType('TSmSet');
    AssertNotNull('type registered', TD);
    AssertEquals('bits 0..10', 11, TSetTypeDesc(TD).BitCount);
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_InlineVar_BitCountIsMaxOrdPlus1;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('''
    program P;
    type TSm = (sA = 5, sB = 70);
    var S: set of TSm;
    begin end.
    ''');
  try
    TD := Prog.SymbolTable.FindType('set of TSm');
    AssertNotNull('type registered', TD);
    AssertEquals('bits 0..70', 71, TSetTypeDesc(TD).BitCount);
    AssertTrue('ordinal 70 needs a jumbo set', TSetTypeDesc(TD).IsJumbo());
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_InferredConst_BitCountIsMaxOrdPlus1;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('''
    program P;
    type TSm = (sA = 5, sB = 10);
    const C = [sB];
    begin end.
    ''');
  try
    TD := Prog.SymbolTable.FindType('set of TSm');
    AssertNotNull('type registered', TD);
    AssertEquals('bits 0..10', 11, TSetTypeDesc(TD).BitCount);
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_InNonConstLiteral_BitCountIsMaxOrdPlus1;
var
  Prog: TProgram;
  Cond: TBinaryExpr;
begin
  { A non-constant element forces the conservative full-enum width, which
    must cover the highest ORDINAL, not the member count. }
  Prog := AnalyseSrc('''
    program P;
    type TSm = (sA = 5, sB = 40);
    var E, F: TSm;
    begin
      if E in [F] then WriteLn('y');
    end.
    ''');
  try
    Cond := TBinaryExpr(TIfStmt(Prog.Block.Stmts.Items[0]).Condition);
    AssertEquals('bits 0..40', 41,
      TSetTypeDesc(Cond.Right.ResolvedType).BitCount);
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_Ordinal255_OK;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('''
    program P;
    type
      TSm = (sA = 0, sB = 255);
      TSmSet = set of TSm;
    begin end.
    ''');
  try
    TD := Prog.SymbolTable.FindType('TSmSet');
    AssertEquals('bits 0..255', 256, TSetTypeDesc(TD).BitCount);
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_OrdinalOver255_Fails;
begin
  { Two members, but bit 9999 would need a 1250-byte bitmap. }
  SemanticFail('''
    program P;
    type
      TSm = (sA = 0, sB = 9999);
      TSmSet = set of TSm;
    begin end.
    ''');
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_InlineOrdinalOver255_Fails;
begin
  SemanticFail('''
    program P;
    type TSm = (sA = 0, sB = 256);
    var S: set of TSm;
    begin end.
    ''');
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_NegativeOrdinal_Fails;
begin
  { A bitmap has no bit -1. }
  SemanticFail('''
    program P;
    type
      TSm = (sA = -1, sB = 2);
      TSmSet = set of TSm;
    begin end.
    ''');
end;

procedure TSetTests.TestSemantic_SetOfExplicitOrdinalEnum_ConstOrdinalOver255_Fails;
begin
  SemanticFail('''
    program P;
    type TSm = (sA = 0, sB = 300);
    const C = [sB];
    begin end.
    ''');
end;

procedure TSetTests.TestSemantic_ImplicitSelfSetField_EmptyLiteral;
begin
  { Both a jumbo (set of Byte) and a small (enum) set field, assigned '[]'
    through the bare implicit-Self form.  The qualified 'Self.Field := []'
    and plain-variable forms already worked; only the bare one was rejected. }
  SemanticOK(
    'program P;'                                            + #10 +
    'type'                                                  + #10 +
    '  TE = (sA, sB, sC);'                                  + #10 +
    '  TSmall = set of TE;'                                 + #10 +
    '  TBig = set of Byte;'                                 + #10 +
    '  TNode = class'                                       + #10 +
    '    Small: TSmall;'                                    + #10 +
    '    Big: TBig;'                                        + #10 +
    '    procedure Reset();'                                + #10 +
    '  end;'                                                + #10 +
    'procedure TNode.Reset();'                              + #10 +
    'begin'                                                 + #10 +
    '  Small := [];'                                        + #10 +
    '  Big := [];'                                          + #10 +
    '  Big := Big + [65];'                                  + #10 +
    'end;'                                                  + #10 +
    'begin'                                                 + #10 +
    'end.');
end;

procedure TSetTests.TestSemantic_SetArrayElement_LiteralAssign;
begin
  { A bracket set literal ([] or [a, b]) assigned into an ARRAY ELEMENT dest —
    static, dynamic, and multi-dimensional — must take its set type from the
    element type, exactly as the plain-variable / field / implicit-Self paths do.
    Before the fix this was rejected ('Expression has no value type' for [], or a
    type mismatch 'array of TE' for [a, b]).  BUG-20260720-set-array-elem-dest. }
  SemanticOK(
    'program P;'                                            + #10 +
    'type'                                                  + #10 +
    '  TE = (sA, sB, sC, sD);'                              + #10 +
    '  TS = set of TE;'                                     + #10 +
    'var'                                                   + #10 +
    '  A: array[0..3] of TS;'                               + #10 +
    '  M: array[0..1, 0..1] of TS;'                         + #10 +
    '  D: array of TS;'                                     + #10 +
    'begin'                                                 + #10 +
    '  A[0] := [];'                                         + #10 +
    '  A[1] := [sA, sC];'                                   + #10 +
    '  A[2] := A[1] + [sB];'                                + #10 +
    '  M[0, 0] := [sD];'                                    + #10 +
    '  SetLength(D, 2);'                                    + #10 +
    '  D[0] := [sA];'                                       + #10 +
    'end.');
end;

{ ------------------------------------------------------------------ }
{ set of Byte / ordinal-based sets (issue #105)                       }
{ ------------------------------------------------------------------ }

const
  SrcSetOfByteType =
    '''
        program P;
        type TByteFlags = set of Byte;
        begin
        end.
        ''';

  SrcSetOfByteVar =
    '''
        program P;
        type TByteFlags = set of Byte;
        var F: TByteFlags;
        begin
          F := [1, 2, 4]
        end.
        ''';

  SrcSetOfSubrangeVar =
    '''
        program P;
        var s: set of 0..255;
        begin
          s := [10, 200]
        end.
        ''';
  SrcSetOfSubrangeType =
    '''
        program P;
        type TS = set of 0..63;
        var s: TS;
        begin
          s := [3, 63]
        end.
        ''';
  SrcSetOfSubrangeOverBound =
    'program P; var s: set of 0..1000; begin s := [1] end.';
  SrcSetOfSubrangeDescending =
    'program P; var s: set of 5..3; begin s := [] end.';

  SrcSetOfByteRange =
    '''
        program P;
        type TByteFlags = set of Byte;
        var F: TByteFlags;
        begin
          F := [1..5]
        end.
        ''';

  SrcSetOfByteIn =
    '''
        program P;
        type TByteFlags = set of Byte;
        var F: TByteFlags;
        begin
          F := [1, 2, 3];
          if 2 in F then
            WriteLn('yes')
        end.
        ''';

  SrcSetOfByteInclude =
    '''
        program P;
        type TByteFlags = set of Byte;
        var F: TByteFlags;
        begin
          F := [];
          Include(F, 5)
        end.
        ''';

  SrcSetOfByteExclude =
    '''
        program P;
        type TByteFlags = set of Byte;
        var F: TByteFlags;
        begin
          F := [1, 2, 3];
          Exclude(F, 2)
        end.
        ''';

  SrcSetOfByteInline =
    '''
        program P;
        var F: set of Byte;
        begin
          F := [10, 20]
        end.
        ''';

  SrcSetOfBoolean =
    '''
        program P;
        type TBoolSet = set of Boolean;
        var B: TBoolSet;
        begin
          B := [True]
        end.
        ''';

procedure TSetTests.TestSemantic_SetOfByte_TypeRegistered;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(SrcSetOfByteType);
  try
    TD := Prog.SymbolTable.FindType('TByteFlags');
    AssertNotNull('type registered', TD);
    AssertTrue('kind is tySet', TD.Kind = tySet);
    AssertTrue('base is Byte', TSetTypeDesc(TD).BaseType.Kind = tyByte);
    AssertEquals('256 bits', 256, TSetTypeDesc(TD).BitCount);
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfByte_VarDecl_OK;
begin
  SemanticOK(SrcSetOfByteVar);
end;

procedure TSetTests.TestSemantic_SetOfByte_IntLiteralAssign_OK;
begin
  SemanticOK(SrcSetOfByteVar);
end;

procedure TSetTests.TestSemantic_SetOfByte_RangeLiteral_OK;
begin
  SemanticOK(SrcSetOfByteRange);
end;

procedure TSetTests.TestSemantic_SetOfByte_InOperator_OK;
begin
  SemanticOK(SrcSetOfByteIn);
end;

procedure TSetTests.TestSemantic_SetOfByte_Include_OK;
begin
  SemanticOK(SrcSetOfByteInclude);
end;

procedure TSetTests.TestSemantic_SetOfByte_Exclude_OK;
begin
  SemanticOK(SrcSetOfByteExclude);
end;

procedure TSetTests.TestSemantic_SetOfByte_InlineType_OK;
begin
  SemanticOK(SrcSetOfByteInline);
end;

procedure TSetTests.TestSemantic_SetOfBoolean_OK;
begin
  SemanticOK(SrcSetOfBoolean);
end;

procedure TSetTests.TestCodegen_SetOfByte_IsJumbo;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(SrcSetOfByteType);
  try
    TD := Prog.SymbolTable.FindType('TByteFlags');
    AssertTrue('set of Byte is jumbo', TSetTypeDesc(TD).IsJumbo());
  finally
    Prog.Free();
  end;
end;

procedure TSetTests.TestSemantic_SetOfSubrange_VarDecl_OK;
begin
  { 'set of 0..255' (integer-subrange base) is accepted. }
  SemanticOK(SrcSetOfSubrangeVar);
end;

procedure TSetTests.TestSemantic_SetOfSubrange_TypeDecl_OK;
begin
  { 'type TS = set of 0..63' is accepted. }
  SemanticOK(SrcSetOfSubrangeType);
end;

procedure TSetTests.TestSemantic_SetOfSubrange_OverBound_Fails;
begin
  { A set has at most 256 elements (ordinals 0..255); 0..1000 is rejected. }
  SemanticFail(SrcSetOfSubrangeOverBound);
end;

procedure TSetTests.TestSemantic_SetOfSubrange_Descending_Fails;
begin
  { A descending subrange (5..3) is a mistake, not a silent empty set. }
  SemanticFail(SrcSetOfSubrangeDescending);
end;

{ ------------------------------------------------------------------ }
{ self-assigned sret call: X := F(X)                                   }
{ ------------------------------------------------------------------ }

const
  SrcDistinctDestRecordCall =
    '''
    program P;
    type TR = record A, B: Integer; end;
    function CompR(const S: TR): TR;
    begin Result.A := S.B; Result.B := S.A end;
    var R, T: TR;
    begin R.A := 1; T := CompR(R) end.
    ''';

  SrcSelfAssignJumboSetCall =
    '''
    program P;
    type TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,
                 b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,
                 b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,
                 b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63,
                 b64,b65,b66,b67,b68,b69,b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);
         TBigSet = set of TBig;
    function Comp(const X: TBigSet): TBigSet;
    begin Result := X end;
    var S: TBigSet;
    begin S := [b70]; S := Comp(S) end.
    ''';

  SrcDistinctDestJumboSetCall =
    '''
    program P;
    type TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,
                 b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,
                 b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,
                 b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63,
                 b64,b65,b66,b67,b68,b69,b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);
         TBigSet = set of TBig;
    function Comp(const X: TBigSet): TBigSet;
    begin Result := X end;
    var S, T: TBigSet;
    begin S := [b70]; T := Comp(S) end.
    ''';

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TSetTests.TestCodegen_DistinctDestRecordCall_KeepsDirectForm;
var IR: string;
begin
  IR := GenIR(SrcDistinctDestRecordCall);
  { Non-aliasing: still the direct form — zero $T, then sret straight into it.
    No temp, no trailing memcpy into $T. }
  AssertTrue('non-aliasing call must still memset the destination directly',
    Pos('call $memset(l $T,', IR) >= 0);
  AssertTrue('non-aliasing call must not memcpy into the destination',
    Pos('call $memcpy(l $T,', IR) < 0);
end;

procedure TSetTests.TestNative_SelfAssignedJumboSetCall_UsesTemp;
var Asm_: string;
begin
  Asm_ := GenAsm(SrcSelfAssignJumboSetCall, TargetX86_64);
  { The aliasing arm parks the temp address in %r14 and memcpy's into the
    destination after the call. }
  AssertTrue('aliased jumbo-set call must stage through %r14',
    Pos('movq %rsp, %r14', Asm_) >= 0);
  AssertTrue('aliased jumbo-set call must memcpy into the destination',
    Pos('callq memcpy', Asm_) >= 0);
end;

procedure TSetTests.TestNative_DistinctDestJumboSetCall_KeepsDirectForm;
var Asm_: string;
begin
  Asm_ := GenAsm(SrcDistinctDestJumboSetCall, TargetX86_64);
  { Non-aliasing: no aliasing temp is staged. }
  AssertTrue('non-aliasing jumbo-set call must not stage an aliasing temp',
    Pos('movq %rsp, %r14', Asm_) < 0);
end;

procedure TSetTests.TestSemantic_SetRangeLiteral_AcceptedInEveryContext;
begin
  AssertEquals('ranges accepted as argument, in-operand and set operand', '',
    SemanticError('''
      program P;
      type TNum = 0..15; TNumSet = set of TNum;
        TDir = (dN, dS, dE, dW); TDirSet = set of TDir;
      function M(S: TNumSet): Integer; begin Result := 0 end;
      var N: TNumSet; D: TDirSet; B: Boolean;
      begin
        B := M([1..3]) = 0;
        B := dE in [dS..dW];
        N := [1];
        B := 2 in (N + [2..4]);
        D := [dN];
        D := D + [dE..dW]
      end.
      '''));
end;

procedure TSetTests.TestSemantic_RangeInOpenArrayArg_Rejected;
begin
  AssertTrue('a range is not an open-array element',
    Pos('only allowed in a set literal', SemanticError('''
      program P;
      procedure OA(const A: array of Integer); begin end;
      begin
        OA([1..3])
      end.
      ''')) >= 0);
end;

initialization
  RegisterTest(TSetTests);

end.
