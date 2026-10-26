{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.semantic;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TSemanticTests = class(TTestCase)
  private
    function Analyse(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { @ takes the address of storage -- a variable, field, element or P^ -- and
      rejects a value with nowhere to point at }
    procedure TestAddrOf_RequiresStorage;
    { an element write through a non-indexed array property follows its read
      specifier }
    procedure TestArrayPropertyElementWrite_FollowsReadField;
    { @S[N] is the address of one byte: a ^Byte, of a variable or field only }
    procedure TestAddrOfStringByte_IsPointerToByte;
    { a class array const may be written with a named array type
      (const CA: TArr = (...)), as a unit-level const may }
    procedure TestClassArrayConst_NamedArrayType;
    { inside a method a record field shadows a same-named global in a field
      access (R.N), as it does for a bare identifier }
    procedure TestFieldAccess_FieldShadowsGlobal_InMethod;
    procedure TestSemantic_WriteFieldWidth_LowersToFormat;
    { Succ/Pred take any ordinal -- Boolean too -- and no float (found by
      the ordinal matrix) }
    procedure TestSemantic_SuccPred_Boolean_Accepted;
    procedure TestSemantic_SuccPred_Float_Rejected;
    { Succ/Pred of a 64-bit value step in 64 bits (x86-64 used addl/subl) }
    procedure TestCodegen_SuccPred_Int64_64BitStep;
    procedure TestSemantic_WriteFieldWidth_DecimalsOnInteger_Rejected;
    procedure TestSemantic_WriteFieldWidth_NonIntegerWidth_Rejected;
    procedure TestSemantic_WriteFieldWidth_UnsupportedType_Rejected;
    { Variable declarations are added to the symbol table }
    procedure TestVarDecl_RegistersSymbol;
    procedure TestVarDecl_Type_Integer;
    procedure TestVarDecl_Type_String;
    procedure TestVarDecl_MultiName_BothRegistered;
    procedure TestVarDecl_UnknownType_RaisesError;
    procedure TestVarDecl_Duplicate_RaisesError;
    { A variable may not share a name with ANY visible type (issue #102):
      same-block, outer-scope, imported, or built-in.  Stricter than FPC
      mode objfpc (which allows shadowing built-in/outer types); Blaise
      rejects the whole class to eliminate the confusion.  Case-insensitive. }
    procedure TestVarDecl_DuplicatesType_RaisesError;
    procedure TestVarDecl_DuplicatesType_DifferentCase_RaisesError;
    procedure TestVarDecl_DuplicatesInterfaceType_RaisesError;
    procedure TestVarDecl_ShadowsBuiltinType_RaisesError;
    procedure TestVarDecl_ShadowsOuterScopeType_RaisesError;
    procedure TestVarDecl_SharesEnumMemberName_OK;
    { Const then var with same name in same block is a duplicate }
    procedure TestVarDecl_DuplicatesConst_RaisesError;
    { Const redeclared with same name in same block is a duplicate }
    procedure TestConst_Duplicate_RaisesError;

    { Module names are reserved identifiers (issue #84).  The program
      name and the names of directly used units cannot be redeclared
      by any top-level declaration, matching FPC and Delphi.  Inner
      scopes may shadow them. }
    procedure TestModuleName_RedeclaredAsVar_RaisesError;
    procedure TestModuleName_RedeclaredAsConst_RaisesError;
    procedure TestModuleName_RedeclaredAsType_RaisesError;
    procedure TestModuleName_RedeclaredAsProc_RaisesError;
    procedure TestModuleName_LocalShadow_OK;
    procedure TestModuleName_NotUsableAsExpression_RaisesError;
    procedure TestUsedUnitName_RedeclaredAsVar_RaisesError;
    { a program named after a unit it uses: on x86-64 its globals were taken
      for the unit's and never defined }
    procedure TestProgramName_SameAsUsedUnit_RaisesError;

    { Expression type inference }
    procedure TestExpr_IntLiteral_TypeIsInteger;
    procedure TestExpr_StringLiteral_TypeIsString;
    procedure TestExpr_Ident_ResolvesToVarType;
    procedure TestExpr_Ident_Undeclared_RaisesError;
    procedure TestExpr_Add_TwoIntegers_TypeIsInteger;
    procedure TestExpr_Add_IntAndString_RaisesError;
    procedure TestExpr_Sub_TypeIsInteger;
    procedure TestExpr_Mul_TypeIsInteger;
    procedure TestExpr_Div_TypeIsInteger;

    { Assignment type checking }
    procedure TestAssign_IntToInt_OK;
    procedure TestAssign_StringToString_OK;
    procedure TestAssign_IntToString_RaisesError;
    procedure TestAssign_StringToInt_RaisesError;
    procedure TestAssign_UndeclaredVar_RaisesError;

    { Procedure calls }
    procedure TestProcCall_WriteLn_NoArgs_OK;
    procedure TestProcCall_WriteLn_StringArg_OK;
    procedure TestProcCall_WriteLn_IntArg_OK;
    procedure TestProcCall_WriteLn_ProceduralArg_RaisesError;
    procedure TestProcCall_WriteLn_ProcCallResult_RaisesError;
    procedure TestProcCall_UndeclaredProc_RaisesError;

    { Full program analysis }
    procedure TestProgram_HelloWorld_OK;
    procedure TestProgram_ArithmeticAndPrint_OK;

    { var/const open-array element write (issue #130 bug5) }
    procedure TestVarOpenArray_ElementWrite_OK;
    procedure TestConstOpenArray_ElementWrite_RaisesError;

    { an ordinal cast of a float and Ord of a float are errors (FPC and
      Delphi agree): the backends reinterpreted a float variable's bits
      (Integer(3.7) was -1717986918) and had no lowering for a float
      expression.  Ordinal casts of ordinals and Double(I) still compile. }
    procedure TestSemantic_OrdinalCastOfFloat_Rejected;
    procedure TestSemantic_OrdOfFloat_Rejected;
    { a value-returning builtin called as a statement (result discarded) is
      lowered to its expression form, so it gets the expression path's
      argument checks and every backend's existing expression lowering }
    procedure TestBuiltinFunctionStatement_LowersToExpressionCall;
    procedure TestBuiltinFunctionStatement_ChecksArguments;
    { a float is rejected wherever an integer is required: the operands of
      and/or/xor, the shifts and mod; the integer arguments of Inc/Dec,
      SetLength, Chr, IntToStr, Copy, Delete, Halt, GetMem, ReallocMem,
      Sleep and ParamStr; string, PChar and array indices, including an
      array field's.  Each compiled and used the float's bit pattern, or
      reached a backend with no integer lowering. }
    procedure TestSemantic_FloatWhereIntegerRequired_Rejected;
  end;

implementation

function TSemanticTests.Analyse(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TSemanticTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := Analyse(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Var declarations                                                    }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestVarDecl_RegistersSymbol;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := Analyse('program P; var x: Integer; begin end.');
  try
    AssertEquals('1 decl', 1, Prog.Block.Decls.Count);
    Decl := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertNotNull('ResolvedType set', Decl.ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestVarDecl_Type_Integer;
var
  Prog: TProgram;
begin
  Prog := Analyse('program P; var n: Integer; begin end.');
  try
    AssertEquals('Integer kind',
      Ord(tyInteger),
      Ord(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestVarDecl_Type_String;
var
  Prog: TProgram;
begin
  Prog := Analyse('program P; var s: string; begin end.');
  try
    AssertEquals('string kind',
      Ord(tyString),
      Ord(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestVarDecl_MultiName_BothRegistered;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := Analyse('program P; var x, y: Integer; begin end.');
  try
    Decl := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertNotNull('ResolvedType', Decl.ResolvedType);
    AssertEquals('Integer', Ord(tyInteger), Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestVarDecl_UnknownType_RaisesError;
begin
  AnalyseExpectError('program P; var x: Foobar; begin end.');
end;

procedure TSemanticTests.TestVarDecl_Duplicate_RaisesError;
begin
  AnalyseExpectError(
    'program P; var x: Integer; x: string; begin end.');
end;

procedure TSemanticTests.TestVarDecl_DuplicatesType_RaisesError;
begin
  AnalyseExpectError(
    'program P; type TFoo = record X: Integer; end; var TFoo: Integer; begin end.');
end;

procedure TSemanticTests.TestVarDecl_DuplicatesType_DifferentCase_RaisesError;
begin
  { The exact issue #102 reproduction: type Iface, var iface — same
    identifier, different case.  Pascal is case-insensitive. }
  AnalyseExpectError(
    'program P; type Iface = interface procedure Test; end; ' +
    'var iface: Iface; begin end.');
end;

procedure TSemanticTests.TestVarDecl_DuplicatesInterfaceType_RaisesError;
begin
  AnalyseExpectError(
    'program P; type IThing = interface procedure Go; end; ' +
    'var IThing: Integer; begin end.');
end;

procedure TSemanticTests.TestVarDecl_ShadowsBuiltinType_RaisesError;
begin
  { Unlike FPC, Blaise rejects a var that shadows a built-in type name —
    `var Integer` is almost always a mistake and shadowing it silently
    redefines the type for the rest of the scope. }
  AnalyseExpectError('program P; var Integer: Int64; begin end.');
end;

procedure TSemanticTests.TestVarDecl_ShadowsOuterScopeType_RaisesError;
begin
  { A type declared in an outer scope may not be shadowed by a local var —
    Blaise rejects the whole var/type name-clash class regardless of scope. }
  AnalyseExpectError(
    'program P; type TFoo = record X: Integer; end; ' +
    'procedure Q; var TFoo: Integer; begin end; ' +
    'begin Q(); end.');
end;

procedure TSemanticTests.TestVarDecl_SharesEnumMemberName_OK;
var
  Prog: TProgram;
begin
  { A variable may share a name with an enum member.  Enum members are not
    bare global symbols, so there is no collision: the variable wins by normal
    scoping and the member stays reachable through its type (TC.C).  Here 'c'
    shares the name of member 'C' (names are case-insensitive). }
  Prog := Analyse('program P; type TC = (A, B, C); var c: TC; begin end.');
  Prog.Free();
end;

procedure TSemanticTests.TestVarDecl_DuplicatesConst_RaisesError;
begin
  AnalyseExpectError(
    'program P; const b = 42; var b: Integer; begin end.');
end;

procedure TSemanticTests.TestConst_Duplicate_RaisesError;
begin
  AnalyseExpectError(
    'program P; const b = 42; b = 99; begin end.');
end;

{ ------------------------------------------------------------------ }
{ Module names are reserved identifiers (issue #84)                   }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestModuleName_RedeclaredAsVar_RaisesError;
begin
  AnalyseExpectError('program P; var P: Integer; begin end.');
end;

procedure TSemanticTests.TestModuleName_RedeclaredAsConst_RaisesError;
begin
  AnalyseExpectError('program P; const P = 1; begin end.');
end;

procedure TSemanticTests.TestModuleName_RedeclaredAsType_RaisesError;
begin
  AnalyseExpectError('program P; type P = record X: Integer; end; begin end.');
end;

procedure TSemanticTests.TestModuleName_RedeclaredAsProc_RaisesError;
begin
  AnalyseExpectError('program P; procedure P; begin end; begin end.');
end;

procedure TSemanticTests.TestModuleName_LocalShadow_OK;
begin
  { An inner scope may shadow the module name, as in FPC/Delphi. }
  Analyse(
    'program P; procedure Q; var P: Integer; begin P := 1; end; ' +
    'begin Q(); end.'
  ).Free();
end;

procedure TSemanticTests.TestProgramName_SameAsUsedUnit_RaisesError;
var
  Err: string;
begin
  Err := SemanticError('program sysutils; uses SysUtils; begin end.');
  AssertTrue(Err, Pos('has the same name as the unit', Err) >= 0);
end;

procedure TSemanticTests.TestModuleName_NotUsableAsExpression_RaisesError;
begin
  { The module name is reserved but is not a value — using it in an
    expression resolves to nothing. }
  AnalyseExpectError('program P; var x: Integer; begin x := P; end.');
end;

procedure TSemanticTests.TestUsedUnitName_RedeclaredAsVar_RaisesError;
begin
  AnalyseExpectError('program P; uses foo; var foo: Integer; begin end.');
end;

{ ------------------------------------------------------------------ }
{ Expression type inference                                           }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestExpr_IntLiteral_TypeIsInteger;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := Analyse('program P; var n: Integer; begin n := 42 end.');
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertNotNull('Expr type', Assign.Expr.ResolvedType);
    AssertEquals('Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_StringLiteral_TypeIsString;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := Analyse(
    'program P; var s: string; begin s := ''hello'' end.');
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertEquals('string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_Ident_ResolvesToVarType;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var x, y: Integer; begin y := x + 1 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertNotNull('Left type', Bin.Left.ResolvedType);
    AssertEquals('x is Integer',
      Ord(tyInteger), Ord(Bin.Left.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_Ident_Undeclared_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; begin n := undeclared end.');
end;

procedure TSemanticTests.TestExpr_Add_TwoIntegers_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 1 + 2 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Add result is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_Add_IntAndString_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; s: string; begin n := n + s end.');
end;

procedure TSemanticTests.TestExpr_Sub_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 10 - 3 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Sub is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_Mul_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 3 * 4 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Mul is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestExpr_Div_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 8 div 2 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Div is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Assignment type checking                                            }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestAssign_IntToInt_OK;
begin
  Analyse('program P; var n: Integer; begin n := 5 end.').Free();
end;

procedure TSemanticTests.TestAssign_StringToString_OK;
begin
  Analyse(
    'program P; var s: string; begin s := ''hi'' end.').Free();
end;

procedure TSemanticTests.TestAssign_IntToString_RaisesError;
begin
  AnalyseExpectError(
    'program P; var s: string; begin s := 42 end.');
end;

procedure TSemanticTests.TestAssign_StringToInt_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; begin n := ''hello'' end.');
end;

procedure TSemanticTests.TestAssign_UndeclaredVar_RaisesError;
begin
  AnalyseExpectError(
    'program P; begin ghost := 1 end.');
end;

{ ------------------------------------------------------------------ }
{ Procedure calls                                                     }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestProcCall_WriteLn_NoArgs_OK;
begin
  Analyse('program P; begin WriteLn() end.').Free();
end;

procedure TSemanticTests.TestProcCall_WriteLn_StringArg_OK;
begin
  Analyse('program P; begin WriteLn(''Hello'') end.').Free();
end;

procedure TSemanticTests.TestProcCall_WriteLn_IntArg_OK;
begin
  Analyse('program P; begin WriteLn(99) end.').Free();
end;

procedure TSemanticTests.TestProcCall_WriteLn_ProceduralArg_RaisesError;
begin
  AnalyseExpectError(
    '''
    program TestProc;
    type TProc = procedure(A, B: Integer);
    procedure Dummy(A, B: Integer); begin end;
    var V: TProc;
    begin
      V := @Dummy;
      WriteLn(V)
    end.
    ''');
end;

procedure TSemanticTests.TestProcCall_WriteLn_ProcCallResult_RaisesError;
begin
  { writeln(proce(2,3)) where proce is a procedure variable — the call
    returns no value, so passing its result to WriteLn must be an error. }
  AnalyseExpectError(
    '''
    program TestProc;
    type TProc = procedure(A, B: Integer);
    procedure Dummy(A, B: Integer); begin end;
    var V: TProc;
    begin
      V := @Dummy;
      WriteLn(V(1, 2))
    end.
    ''');
end;

procedure TSemanticTests.TestProcCall_UndeclaredProc_RaisesError;
begin
  AnalyseExpectError('program P; begin NoSuchProc() end.');
end;

{ ------------------------------------------------------------------ }
{ Full programs                                                       }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestProgram_HelloWorld_OK;
begin
  Analyse(
    '''
        program Hello;
        begin
          WriteLn('Hello!');
        end.
        '''
  ).Free();
end;

procedure TSemanticTests.TestProgram_ArithmeticAndPrint_OK;
begin
  Analyse(
    '''
        program Arith;
        var n: Integer;
        begin
          n := 3 * 4 + 2;
          WriteLn(n);
        end.
        '''
  ).Free();
end;

procedure TSemanticTests.TestVarOpenArray_ElementWrite_OK;
begin
  { Writing an element of a VAR open-array parameter is allowed. }
  Analyse(
    'program P; ' +
    'procedure Z(var a: array of Integer); begin a[0] := 9 end; ' +
    'var x: array[0..1] of Integer; begin x[0]:=1; x[1]:=2; Z(x) end.').Free();
end;

procedure TSemanticTests.TestConstOpenArray_ElementWrite_RaisesError;
begin
  { Writing an element of a CONST open-array parameter is rejected. }
  AnalyseExpectError(
    'program P; ' +
    'procedure B(const a: array of Integer); begin a[0] := 9 end; ' +
    'var x: array[0..1] of Integer; begin x[0]:=1; x[1]:=2; B(x) end.');
end;

{ Write / WriteLn field widths (semantic lowering to Format). }
procedure TSemanticTests.TestSemantic_SuccPred_Boolean_Accepted;
begin
  AssertEquals('no error', '', SemanticError('''
    program P;
    var B: Boolean;
    begin
      B := Succ(False);
      B := Pred(B);
    end.
    '''));
end;

procedure TSemanticTests.TestSemantic_SuccPred_Float_Rejected;
begin
  AssertTrue('float rejected', Pos('requires an ordinal',
    SemanticError('''
      program P;
      var D: Double;
      begin
        D := Succ(1.5);
      end.
      ''')) >= 0);
end;

procedure TSemanticTests.TestCodegen_SuccPred_Int64_64BitStep;
const
  Src = '''
    program P;
    var V: Int64;
    begin
      V := Pred(V);
      V := Succ(V);
    end.
    ''';
begin
  AssertEquals('64-bit Pred', '',
    AsmMissing(Src, #9'subq $1, %rax', #9'sub x0, x0, #1'));
  AssertEquals('64-bit Succ', '',
    AsmMissing(Src, #9'addq $1, %rax', #9'add x0, x0, #1'));
end;

procedure TSemanticTests.TestSemantic_WriteFieldWidth_LowersToFormat;
var
  Prog: TProgram;
  F: TFuncCallExpr;
begin
  Prog := Analyse('program P; var X: Double; begin WriteLn(X:8:2) end.');
  try
    F := TFuncCallExpr(TProcCall(Prog.Block.Stmts[0]).Args.Items[0]);
    AssertEquals('lowered to Format', 'Format', F.Name);
    AssertTrue('literal spec', TObject(F.Args.Items[0]) is TStringLiteral);
    AssertEquals('fixed-point spec', '%8.2f',
      TStringLiteral(F.Args.Items[0]).Value);
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestSemantic_WriteFieldWidth_DecimalsOnInteger_Rejected;
begin
  AssertTrue('decimals only for a real',
    Pos('only allowed for a real', SemanticError(
      'program P; var I: Integer; begin WriteLn(I:5:2) end.')) >= 0);
end;

procedure TSemanticTests.TestSemantic_WriteFieldWidth_NonIntegerWidth_Rejected;
begin
  AssertTrue('width must be an integer',
    Pos('field width must be an integer', SemanticError(
      'program P; var D: Double; begin WriteLn(D:''x'') end.')) >= 0);
end;

procedure TSemanticTests.TestSemantic_WriteFieldWidth_UnsupportedType_Rejected;
begin
  AssertTrue('a record has no field-width form',
    Pos('not supported for a value', SemanticError(
      'program P; type TR = record A: Integer; end; var R: TR; ' +
      'begin WriteLn(R:5) end.')) >= 0);
end;

procedure TSemanticTests.TestFieldAccess_FieldShadowsGlobal_InMethod;
const
  Src = '''
    program P;
    type
      TRec = record N: Integer; end;
      TObj = class
      public
        R: TRec;
        procedure Direct;
      end;
    var R: TRec;
    procedure TObj.Direct;
    var X: Integer;
    begin
      R.N := 5;
      X := R.N;
    end;
    begin
    end.
    ''';
var
  Prog: TProgram;
  M: TMethodDecl;
  I, J: Integer;
begin
  { inside a method the record FIELD R shadows the global R for a field
    access, exactly as for a bare identifier: R.N read and wrote the global }
  Prog := Analyse(Src);
  try
    { the analysed body hangs off the class's method list }
    M := nil;
    for I := 0 to Prog.Block.TypeDecls.Count - 1 do
      if TTypeDecl(Prog.Block.TypeDecls.Items[I]).Def is TClassTypeDef then
        for J := 0 to TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[I]).Def)
                         .Methods.Count - 1 do
          if (TMethodDecl(TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[I]).Def)
                .Methods.Items[J]).Name = 'Direct') and
             (TMethodDecl(TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[I]).Def)
                .Methods.Items[J]).Body <> nil) then
            M := TMethodDecl(TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[I]).Def)
                   .Methods.Items[J]);
    AssertTrue('method found', M <> nil);
    AssertTrue('method has a body', M.Body <> nil);
    AssertEquals('two statements', 2, M.Body.Stmts.Count);
    AssertTrue('a field assignment', M.Body.Stmts.Items[0] is TFieldAssignment);
    AssertTrue('write: R.N := 5 is Self.R.N',
      TFieldAssignment(M.Body.Stmts.Items[0]).IsImplicitSelf);
    AssertTrue('an assignment', M.Body.Stmts.Items[1] is TAssignment);
    AssertTrue('of a field access',
      TAssignment(M.Body.Stmts.Items[1]).Expr is TFieldAccessExpr);
    AssertTrue('read: X := R.N is Self.R.N',
      TFieldAccessExpr(TAssignment(M.Body.Stmts.Items[1]).Expr).IsImplicitSelf);
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestClassArrayConst_NamedArrayType;
const
  Src = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      public
        const CA: TArr = (5, 6, 7, 8);
      end;
    procedure ShowOpen(const A: array of Integer); begin end;
    begin
      ShowOpen(TObj.CA)
    end.
    ''';
begin
  { a member array const written with a NAMED array type is accepted (it was
    "Unknown element type ''") and, passed as an open array, is addressed
    through its data label on both ISAs (there is no field to address) }
  AssertEquals('accepted', '', SemanticError(Src));
  AssertEquals('the data label is the storage', '',
    AsmMissing(Src, 'leaq TObj_CA(%rip), %rax', 'adrp x0, TObj_CA@PAGE'));
end;

procedure TSemanticTests.TestAddrOfStringByte_IsPointerToByte;
const
  SrcByte = '''
    program P;
    var S: string; Q: ^Byte;
    begin
      Q := @S[1];
    end.
    ''';
  SrcInt = '''
    program P;
    var S: string; Q: ^Integer;
    begin
      Q := @S[1];
    end.
    ''';
  SrcTemp = '''
    program P;
    function F: string; begin Result := 'ab'; end;
    var Q: ^Byte;
    begin
      Q := @F()[1];
    end.
    ''';
begin
  AssertEquals('@S[N] is a ^Byte', '', SemanticError(SrcByte));
  AssertTrue('not a ^Integer', SemanticError(SrcInt) <> '');
  AssertTrue('a byte of a temporary string is rejected',
    Pos('would dangle', SemanticError(SrcTemp)) >= 0);
end;

procedure TSemanticTests.TestArrayPropertyElementWrite_FollowsReadField;
const
  SrcField = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      private
        FArr: TArr;
        procedure SetArr(const V: TArr);
      public
        property AP: TArr read FArr write FArr;
        property AW: TArr read FArr write SetArr;
        procedure Show;
      end;
    procedure TObj.SetArr(const V: TArr); begin end;
    procedure TObj.Show; begin AP[3] := 25; AW[1] := 2; end;
    var O: TObj;
    begin
      O.AP[1] := 11; O.AW[2] := 12;
    end.
    ''';
  SrcGetter = '''
    program P;
    type
      TArr = array[0..3] of Integer;
      TObj = class
      private
        function GetArr: TArr;
        procedure SetArr(const V: TArr);
      public
        property AM: TArr read GetArr write SetArr;
      end;
    function TObj.GetArr: TArr; begin end;
    procedure TObj.SetArr(const V: TArr); begin end;
    var O: TObj;
    begin
      O.AM[2] := 12;
    end.
    ''';
begin
  { an element write through a field-read array property, bare or qualified,
    writes the read field (the bare form was "Undeclared variable"); through
    a getter-read one it is rejected, naming the reason (it was a type
    mismatch against the whole array) }
  AssertEquals('field-read: accepted', '', SemanticError(SrcField));
  AssertTrue('getter-read: rejected with the reason',
    Pos('read through a method', SemanticError(SrcGetter)) >= 0);
end;

procedure TSemanticTests.TestAddrOf_RequiresStorage;
const
  SrcOk = '''
    program P;
    type
      TRec = record N: Integer; A: array[0..1] of Integer; end;
      PRec = ^TRec;
    var X: Integer; R: TRec; PR: PRec; Q: ^Integer; A: array[0..2] of Integer;
    begin
      Q := @X; Q := @R.N; Q := @R.A[1]; Q := @A[2]; PR := @R; Q := @PR^.N;
    end.
    ''';
  SrcCall = '''
    program P;
    function F: Integer; begin Result := 1; end;
    var Q: ^Integer;
    begin
      Q := @F();
    end.
    ''';
  SrcExpr = '''
    program P;
    var Q: ^Integer; X: Integer;
    begin
      Q := @(X + 1);
    end.
    ''';
  SrcConst = '''
    program P;
    const K = 3;
    var Q: ^Integer;
    begin
      Q := @K;
    end.
    ''';
begin
  { @ addresses storage only; a call result, an operator or a scalar constant
    is rejected here (both backends used to fail late, "unsupported
    address-of form") }
  AssertEquals('storage: accepted', '', SemanticError(SrcOk));
  AssertTrue('a call result', Pos('Cannot take the address', SemanticError(SrcCall)) >= 0);
  AssertTrue('an operator', Pos('Cannot take the address', SemanticError(SrcExpr)) >= 0);
  AssertTrue('a constant', Pos('Cannot take the address', SemanticError(SrcConst)) >= 0);
end;

procedure TSemanticTests.TestSemantic_OrdinalCastOfFloat_Rejected;
const
  Pre = 'program P; type TC = (cA, cB); var I: Integer; B: Byte; ' +
    'D: Double; S: Single; E: TC; Ok: Boolean; begin ';
begin
  AssertTrue('a float variable',
    Pos('Illegal type conversion from ''Double'' to ''Integer''',
      SemanticError(Pre + 'I := Integer(D) end.')) >= 0);
  AssertTrue('a float expression',
    Pos('use Trunc or Round',
      SemanticError(Pre + 'I := Integer(I / 2) end.')) >= 0);
  AssertTrue('a float literal',
    Pos('Illegal type conversion', SemanticError(Pre + 'B := Byte(2.5) end.')) >= 0);
  AssertTrue('a Single into Int64',
    Pos('from ''Single'' to ''Int64''',
      SemanticError(Pre + 'WriteLn(Int64(S)) end.')) >= 0);
  AssertTrue('an enum target',
    Pos('Illegal type conversion', SemanticError(Pre + 'E := TC(D) end.')) >= 0);
  AssertTrue('a Boolean target',
    Pos('Illegal type conversion', SemanticError(Pre + 'Ok := Boolean(D) end.')) >= 0);
  AssertEquals('ordinal casts and float conversions still compile', '',
    SemanticError(Pre + 'I := Integer(E) + Byte(I) + Ord(Ok); ' +
      'D := Double(I); S := Single(D); I := Trunc(D) + Round(S) end.'));
end;

procedure TSemanticTests.TestSemantic_OrdOfFloat_Rejected;
begin
  AssertTrue('a float variable',
    Pos('Ord expects an ordinal value, not ''Double''', SemanticError(
      'program P; var D: Double; begin WriteLn(Ord(D)) end.')) >= 0);
  AssertTrue('a float expression',
    Pos('Ord expects an ordinal value', SemanticError(
      'program P; var I: Integer; begin WriteLn(Ord(I / 2)) end.')) >= 0);
end;

procedure TSemanticTests.TestSemantic_FloatWhereIntegerRequired_Rejected;
const
  Pre = 'program P; type TR = record DA: array of Integer; ' +
    'SA: array[0..2] of Integer; end; var I, J: Integer; D: Double; ' +
    'S: string; DA: array of Integer; Pt: Pointer; R: TR; PC: PChar; begin ';

  procedure Rejected(const ABody, AMsg: string);
  var
    Err: string;
  begin
    Err := SemanticError(Pre + ABody + ' end.');
    AssertTrue(ABody + ': ' + Err, Pos(AMsg, Err) >= 0);
  end;

begin
  Rejected('J := I and D', '''and'' requires integer or Boolean operands');
  Rejected('J := I or 2.5', '''or'' requires integer or Boolean operands');
  Rejected('J := I xor (I / 2)', '''xor'' requires integer or Boolean');
  Rejected('J := I shl D', '''shl'' requires integer operands');
  Rejected('J := I mod 2.0', '''mod'' requires integer operands');
  Rejected('Inc(J, D)', 'Second argument of ''Inc'' must be an integer');
  Rejected('Dec(J, I / 2)', 'Second argument of ''Dec'' must be an integer');
  Rejected('Inc(D)', '''Inc'' needs an ordinal or pointer variable');
  Rejected('SetLength(S, D)', 'Length argument of ''SetLength''');
  Rejected('SetLength(DA, D)', 'Length argument of ''SetLength''');
  Rejected('S := Chr(D)', 'argument of ''Chr'' must be an integer');
  Rejected('S := IntToStr(D)', 'argument of ''IntToStr'' must be an integer');
  Rejected('S := Copy(S, D, 1)', 'Index argument of ''Copy''');
  Rejected('S := Copy(S, 0, D)', 'Count argument of ''Copy''');
  Rejected('Delete(S, 0, D)', 'Count argument of ''Delete''');
  Rejected('Halt(D)', 'exit code of ''Halt'' must be an integer');
  Rejected('Pt := GetMem(D)', 'byte count argument of ''GetMem''');
  Rejected('Pt := ReallocMem(Pt, D)', 'byte count argument of ''ReallocMem''');
  Rejected('Sleep(D)', 'argument of ''Sleep'' must be an integer');
  Rejected('S := ParamStr(D)', 'argument of ''ParamStr'' must be an integer');
  Rejected('J := S[D]', 'String subscript index must be an integer');
  Rejected('S[D] := 65', 'String subscript index must be an integer');
  Rejected('J := DA[D]', 'Dynamic array index must be an integer');
  Rejected('DA[D] := 1', 'Dynamic array index must be an integer');
  Rejected('J := PC[D]', 'PChar subscript index must be an integer');
  Rejected('J := R.DA[D]', 'Dynamic array index must be an integer');
  Rejected('J := R.SA[D]', 'Static array index must be an ordinal type');
  AssertEquals('the integer forms still compile', '', SemanticError(Pre +
    'SetLength(DA, 3); SetLength(S, 2); J := (I shl 2) + (I and 3) + ' +
    'I mod 2 + DA[I] + S[I] + R.SA[1]; Inc(J, 2); Dec(J); ' +
    'S := Chr(65) + IntToStr(I) + Copy(S, 0, 1); Delete(S, 0, 1); ' +
    'Pt := GetMem(8); Pt := ReallocMem(Pt, 16); Sleep(0); ' +
    'S := ParamStr(0); if (I > 0) or (J > 0) then Halt(0) end.'));
end;

procedure TSemanticTests.TestBuiltinFunctionStatement_LowersToExpressionCall;
var
  Prog: TProgram;
  PC: TProcCall;
  Call: TASTExpr;
begin
  Prog := Analyse('program P; begin Exec(''true'') end.');
  try
    AssertTrue('a procedure-call statement',
      Prog.Block.Stmts.Items[0] is TProcCall);
    PC := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertTrue('lowered to an expression-call statement',
      PC.LoweredCall is TExprCallStmt);
    Call := TExprCallStmt(PC.LoweredCall).Call;
    AssertTrue('of the builtin function call', Call is TFuncCallExpr);
    AssertEquals('name', 'Exec', TFuncCallExpr(Call).Name);
    AssertEquals('argument', 1, Integer(TFuncCallExpr(Call).Args.Count));
    AssertNotNull('analysed', Call.ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TSemanticTests.TestBuiltinFunctionStatement_ChecksArguments;
begin
  AssertTrue('Exec arity', Pos('Exec requires exactly 1 argument',
    SemanticError('program P; begin Exec(''a'', ''b'') end.')) >= 0);
  AssertTrue('Ord of a float', Pos('Ord expects an ordinal value',
    SemanticError('program P; var D: Double; begin Ord(D) end.')) >= 0);
  AssertEquals('valid statement forms still compile', '', SemanticError(
    'program P; var S: string; begin Exec(''true''); Length(S); ' +
    'Pos(''a'', S); FileExists(S); GetTempDir(); ExtractFileName(S) end.'));
end;

initialization
  RegisterTest(TSemanticTests);

end.
