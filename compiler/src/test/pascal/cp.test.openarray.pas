{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.openarray;

{ Tests for const open array parameters: parsing, semantic analysis,
  and QBE IR code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TOpenArrayTests = class(TTestCase)
  private
    function  ParseSrc(const ASrc: string): TProgram;
    function  AnalyseSrc(const ASrc: string): TProgram;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_OpenArray_IsOpenArray;
    procedure TestParse_OpenArray_ElementTypeName;
    procedure TestParse_OpenArray_IsConstParam;
    procedure TestParse_OpenArray_IntegerElement;
    procedure TestParse_OpenArray_ValueParam_IsNotOpenArray;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_OpenArray_ResolvesToOpenArrayKind;
    procedure TestSemantic_OpenArray_ElementType;
    procedure TestSemantic_High_ReturnsInteger;
    procedure TestSemantic_Low_ReturnsInteger;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Array literal call site                                              }
    { ------------------------------------------------------------------ }
    procedure TestParse_ArrayLiteral_NodeType;
    procedure TestParse_ArrayLiteral_ElementCount;
    procedure TestParse_ArrayLiteral_SingleElement;
    procedure TestSemantic_ArrayLiteral_ResolvesToOpenArray;
    procedure TestSemantic_ArrayLiteral_ElementType;

    { ------------------------------------------------------------------ }
    { Length() on open-array and static-array parameters                  }
    { ------------------------------------------------------------------ }
    { Length(A) on an open-array param must compile (was rejected with
      "Length argument must be a string") and emit High+1 IR. }
    procedure TestSemantic_Length_OpenArray_Accepted;
    { Length(A) on a static-array param emits a compile-time constant. }
    procedure TestSemantic_Length_StaticArray_Accepted;
    { IR: Length(open-array) loads the _high slot and adds 1. }
    { IR: Length(static-array) emits a constant equal to the element count. }

    { ------------------------------------------------------------------ }
    { Static array coerced to open-array parameter                         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StaticArrayToOpenArray_Accepted;
    procedure TestSemantic_StaticArrayToOpenArray_NonZeroBase_Accepted;
    { [0, 4] passed to an 'array of Byte' failed with "No matching overload":
      the literal was typed 'array of Integer' from its first element, and
      no rule let constant integers convert to the formal's element type
      (found via GH #233). }
    procedure TestSemantic_IntLiteralToByteOpenArray_Accepted;
    procedure TestSemantic_NonConstElemToByteOpenArray_Rejected;
    { The literal's element block must be laid out at the FORMAL's width. }
    procedure TestCodegen_IntLiteralToByteOpenArray_ByteStores;
    { BUG-20261010-captured-open-array: a nested routine using its parent's
      open-array parameter captured only the data slot, never '<A>_high', so
      x86-64 linked High(A) against an undefined global (segfault at run
      time) and arm64 rejected it.  The high slot is now captured with it. }
    procedure TestSemantic_NestedCapture_OpenArray_CapturesHighSlot;
    procedure TestCodegen_NestedCapture_OpenArray_NoGlobalHigh;
    { An anonymous method cannot capture an open array (as in Delphi). }
    procedure TestSemantic_AnonCapture_OpenArray_Rejected;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TOpenArrayTests.ParseSrc(const ASrc: string): TProgram;
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

function TOpenArrayTests.AnalyseSrc(const ASrc: string): TProgram;
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
{ Shared source snippets                                              }
{ ------------------------------------------------------------------ }

const
  SrcPrintFirst =
    '''
        program OA;
        procedure PrintFirst(const A: array of string);
        begin
        end;
        begin end.
        ''';

  SrcHighLow =
    '''
        program OA;
        function Len(const A: array of string): Integer;
        var H, L: Integer;
        begin
          H := High(A);
          L := Low(A);
          Result := H - L + 1
        end;
        begin end.
        ''';

  SrcLiteralCall =
    '''
        program OA;
        procedure Print(const A: array of string);
        begin end;
        begin
          Print(['hello', 'world'])
        end.
        ''';

  SrcLiteralSingle =
    '''
        program OA;
        procedure Print(const A: array of string);
        begin end;
        begin
          Print(['only'])
        end.
        ''';

  SrcLengthOpenArray =
    '''
        program OA;
        procedure Show(const A: array of string);
        var N: Integer;
        begin
          N := Length(A)
        end;
        begin
          Show(['x', 'y', 'z'])
        end.
        ''';

  SrcLengthStaticArray =
    '''
        program OA;
        var A: array[1..5] of Integer;
        var N: Integer;
        begin
          N := Length(A)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TOpenArrayTests.TestParse_OpenArray_IsOpenArray;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcPrintFirst);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertTrue('A is open array', Par.IsOpenArray);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_OpenArray_ElementTypeName;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcPrintFirst);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('element type is string', 'string', Par.TypeName);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_OpenArray_IsConstParam;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcPrintFirst);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertTrue('const modifier recorded', Par.IsConstParam);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_OpenArray_IntegerElement;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(
    '''
        program T;
        procedure Sum(const A: array of Integer);
        begin end;
        begin end.
        ''');
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertTrue('A is open array', Par.IsOpenArray);
    AssertEquals('element type is Integer', 'Integer', Par.TypeName);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_OpenArray_ValueParam_IsNotOpenArray;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(
    '''
        program T;
        procedure Foo(X: Integer);
        begin end;
        begin end.
        ''');
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertFalse('plain param is not open array', Par.IsOpenArray);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TOpenArrayTests.TestSemantic_OpenArray_ResolvesToOpenArrayKind;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := AnalyseSrc(SrcPrintFirst);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertNotNull('ResolvedType set', Par.ResolvedType);
    AssertEquals('kind is tyOpenArray', Ord(tyOpenArray), Ord(Par.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_OpenArray_ElementType;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam; OAT: TOpenArrayTypeDesc;
begin
  P := AnalyseSrc(SrcPrintFirst);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertTrue('is TOpenArrayTypeDesc', Par.ResolvedType is TOpenArrayTypeDesc);
    OAT := TOpenArrayTypeDesc(Par.ResolvedType);
    AssertNotNull('ElementType set', OAT.ElementType);
    AssertEquals('element is tyString', Ord(tyString), Ord(OAT.ElementType.Kind));
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_High_ReturnsInteger;
var P: TProgram; MD: TMethodDecl; Assign: TAssignment; FCall: TFuncCallExpr;
begin
  P := AnalyseSrc(SrcHighLow);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);
    { First statement in body: H := High(A) }
    Assign := TAssignment(MD.Body.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertNotNull('High resolved type set', FCall.ResolvedType);
    AssertEquals('High returns tyInteger', Ord(tyInteger), Ord(FCall.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_Low_ReturnsInteger;
var P: TProgram; MD: TMethodDecl; Assign: TAssignment; FCall: TFuncCallExpr;
begin
  P := AnalyseSrc(SrcHighLow);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);
    { Second statement: L := Low(A) }
    Assign := TAssignment(MD.Body.Stmts[1]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertNotNull('Low resolved type set', FCall.ResolvedType);
    AssertEquals('Low returns tyInteger', Ord(tyInteger), Ord(FCall.ResolvedType.Kind));
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Array literal tests                                               }
{ ------------------------------------------------------------------ }

procedure TOpenArrayTests.TestParse_ArrayLiteral_NodeType;
var P: TProgram; Call: TProcCall; Arg: TASTExpr;
begin
  P := ParseSrc(SrcLiteralCall);
  try
    { First statement in the main block is Print([...]) }
    Call := TProcCall(P.Block.Stmts[0]);
    Arg  := TASTExpr(Call.Args[0]);
    AssertTrue('arg is TArrayLiteralExpr', Arg is TArrayLiteralExpr);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_ArrayLiteral_ElementCount;
var P: TProgram; Call: TProcCall; Lit: TArrayLiteralExpr;
begin
  P := ParseSrc(SrcLiteralCall);
  try
    Call := TProcCall(P.Block.Stmts[0]);
    Lit  := TArrayLiteralExpr(TASTExpr(Call.Args[0]));
    AssertEquals('two elements', 2, Lit.Elements.Count);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestParse_ArrayLiteral_SingleElement;
var P: TProgram; Call: TProcCall; Lit: TArrayLiteralExpr;
begin
  P := ParseSrc(SrcLiteralSingle);
  try
    Call := TProcCall(P.Block.Stmts[0]);
    Lit  := TArrayLiteralExpr(TASTExpr(Call.Args[0]));
    AssertEquals('one element', 1, Lit.Elements.Count);
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_ArrayLiteral_ResolvesToOpenArray;
var P: TProgram; Call: TProcCall; Arg: TASTExpr;
begin
  P := AnalyseSrc(SrcLiteralCall);
  try
    Call := TProcCall(P.Block.Stmts[0]);
    Arg  := TASTExpr(Call.Args[0]);
    AssertNotNull('ResolvedType set', Arg.ResolvedType);
    AssertEquals('kind is tyOpenArray', Ord(tyOpenArray), Ord(Arg.ResolvedType.Kind));
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_ArrayLiteral_ElementType;
var P: TProgram; Call: TProcCall; Arg: TASTExpr; OAT: TOpenArrayTypeDesc;
begin
  P := AnalyseSrc(SrcLiteralCall);
  try
    Call := TProcCall(P.Block.Stmts[0]);
    Arg  := TASTExpr(Call.Args[0]);
    AssertTrue('is TOpenArrayTypeDesc', Arg.ResolvedType is TOpenArrayTypeDesc);
    OAT := TOpenArrayTypeDesc(Arg.ResolvedType);
    AssertEquals('element is tyString', Ord(tyString), Ord(OAT.ElementType.Kind));
  finally P.Free(); end;
end;

procedure TOpenArrayTests.TestSemantic_Length_OpenArray_Accepted;
var P: TProgram;
begin
  P := AnalyseSrc(SrcLengthOpenArray);
  P.Free();
  AssertTrue('no error raised', True);
end;

procedure TOpenArrayTests.TestSemantic_Length_StaticArray_Accepted;
var P: TProgram;
begin
  P := AnalyseSrc(SrcLengthStaticArray);
  P.Free();
  AssertTrue('no error raised', True);
end;

{ ------------------------------------------------------------------ }
{ Static array coerced to open-array — source constants               }
{ ------------------------------------------------------------------ }

const
  SrcStaticToOpen =
    '''
        program P;
        procedure Show(const A: array of Integer);
        var N: Integer;
        begin
          N := Length(A)
        end;
        var B: array[0..3] of Integer;
        begin
          Show(B)
        end.
        ''';

  SrcStaticToOpenNonZero =
    '''
        program P;
        procedure Show(const A: array of Integer);
        var N: Integer;
        begin
          N := Length(A)
        end;
        var B: array[3..7] of Integer;
        begin
          Show(B)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Static array coerced to open-array — tests                           }
{ ------------------------------------------------------------------ }

procedure TOpenArrayTests.TestSemantic_StaticArrayToOpenArray_Accepted;
var P: TProgram;
begin
  P := AnalyseSrc(SrcStaticToOpen);
  P.Free();
  AssertTrue('static array passed to open-array param compiles', True);
end;

procedure TOpenArrayTests.TestSemantic_StaticArrayToOpenArray_NonZeroBase_Accepted;
var P: TProgram;
begin
  P := AnalyseSrc(SrcStaticToOpenNonZero);
  P.Free();
  AssertTrue('non-zero-base static array passed to open-array param compiles', True);
end;

const
  SrcIntLitToByteOpen =
    '''
        program P;
        const K = 9;
        procedure Show(const A: array of Byte);
        begin
          WriteLn(Length(A))
        end;
        begin
          Show([7, 250, K, 1 + 2])
        end.
        ''';

procedure TOpenArrayTests.TestSemantic_IntLiteralToByteOpenArray_Accepted;
begin
  AnalyseSrc(SrcIntLitToByteOpen).Free();
end;

procedure TOpenArrayTests.TestSemantic_NonConstElemToByteOpenArray_Rejected;
var
  Raised: Boolean;
begin
  { an Integer VARIABLE is not an untyped constant: no implicit narrowing }
  Raised := False;
  try
    AnalyseSrc(
      '''
          program P;
          procedure Show(const A: array of Byte);
          begin
          end;
          var N: Integer;
          begin
            Show([N, 1])
          end.
          ''').Free();
  except
    on E: ESemanticError do
      Raised := True;
  end;
  AssertTrue('an Integer variable element is not narrowed', Raised);
end;

procedure TOpenArrayTests.TestCodegen_IntLiteralToByteOpenArray_ByteStores;
begin
  AssertEquals('literal element stored one byte wide', '',
    AsmMissing(SrcIntLitToByteOpen, #9'movb %al, 1(%rsp)', #9'strb w0, [x9]'));
end;

const
  SrcNestedOpenArray =
    '''
        program P;
        procedure Show(const A: array of Integer);
          procedure Inner;
          var I: Integer;
          begin
            for I := 0 to High(A) do
              WriteLn(A[I])
          end;
        begin
          Inner()
        end;
        begin
          Show([1, 2])
        end.
        ''';

procedure TOpenArrayTests.TestSemantic_NestedCapture_OpenArray_CapturesHighSlot;
var
  Prog: TProgram;
  Outer, Inner: TMethodDecl;
begin
  Prog := AnalyseSrc(SrcNestedOpenArray);
  try
    Outer := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    Inner := TMethodDecl(Outer.Body.ProcDecls.Items[0]);
    AssertNotNull('Inner captured something', Inner.CapturedVars);
    AssertTrue('data slot captured', Inner.CapturedVars.IndexOf('A') >= 0);
    AssertTrue('high slot captured', Inner.CapturedVars.IndexOf('A_high') >= 0);
    AssertTrue('recognised as an open-array capture',
      Inner.CapturesOpenArray('A'));
  finally
    Prog.Free();
  end;
end;

procedure TOpenArrayTests.TestCodegen_NestedCapture_OpenArray_NoGlobalHigh;
var
  X86: string;
begin
  { arm64 raised NotYet while generating; x86-64 named a global }
  X86 := GenAsm(SrcNestedOpenArray, TargetX86_64);
  AssertTrue('x86-64: no global A_high reference', Pos('A_high(%rip)', X86) < 0);
  AssertTrue('arm64: generates', GenAsm(SrcNestedOpenArray, TargetArm64) <> '');
end;

procedure TOpenArrayTests.TestSemantic_AnonCapture_OpenArray_Rejected;
var
  Msg: string;
begin
  Msg := '';
  try
    AnalyseSrc(
      '''
          program P;
          type TF = reference to function: Integer;
          function Make(const A: array of Integer): TF;
          begin
            Result := function: Integer begin Result := High(A) end
          end;
          begin
            WriteLn(Make([1])())
          end.
          ''').Free();
  except
    on E: ESemanticError do
      Msg := E.Message;
  end;
  AssertTrue('rejected with an open-array capture message: ' + Msg,
    Pos('Cannot capture open-array parameter', Msg) >= 0);
end;

initialization
  RegisterTest(TOpenArrayTests);

end.
