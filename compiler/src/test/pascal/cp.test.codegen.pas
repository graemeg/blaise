{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.codegen;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe,
  blaise.codegen.native, blaise.codegen.target;

type
  TCodeGenTests = class(TTestCase)
  private
    function GenerateIR(const ASrc: string): string;
    function GenerateNativeAsm(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Data sections }
    procedure TestHelloWorld_HasStrLitData;
    procedure TestHelloWorld_UsesSysWriteStr;

    { Main function structure }
    procedure TestOutput_HasMainFunction;
    procedure TestOutput_HasRetZero;
    procedure TestMain_CallsBlaiseInit;
    procedure TestMain_Native_CallsBlaiseInit;

    { WriteLn }
    procedure TestWriteLn_NoArgs_CallsSysWriteNewline;
    procedure TestWriteLn_StringLit_CallsSysWriteStr;
    procedure TestWriteLn_IntExpr_CallsSysWriteInt;
    procedure TestWriteLn_BoolExpr_CallsSysWriteBool;

    { Variables and assignment }
    procedure TestIntVar_HasAlloc;
    procedure TestAssignment_HasStorew;
    procedure TestAssignment_LoadAndStore;

    { Arithmetic }
    procedure TestAdd_EmitsAddInstruction;
    procedure TestMul_EmitsMulInstruction;

    { Header comment }
    procedure TestOutput_HasSourceComment;

    { String equality }
    procedure TestStringEq_EmitsStringEquals;
    procedure TestStringNe_EmitsStringEqualsNegated;
    procedure TestStringEq_SemanticCompiles;

    { True / False built-in constants }
    procedure TestTrue_EmitsCopyOne;
    procedure TestFalse_EmitsCopyZero;
    procedure TestTrue_AssignToBoolVar;
    procedure TestFalse_AssignToBoolVar;
    procedure TestTrue_InIfCondition;
    procedure TestBoolFunc_ReturnTrue;

    { Case-insensitive identifier normalisation }
    procedure TestResult_LowercaseAssign_CompilesOK;
    procedure TestIdent_WrongCase_NormalisedInIR;
    procedure TestFieldAccess_WrongCase_NormalisedInIR;
    procedure TestForLoop_WrongCase_NormalisedInIR;
    procedure TestFuncCall_WrongCase_NormalisedInIR;
    procedure TestAssign_WrongCase_NormalisedInIR;
    procedure TestMethodCallObj_WrongCase_NormalisedInIR;

    { Int64 to Double conversion }
    procedure TestInt64MulDouble_EmitsSltof;
    procedure TestIntMulDouble_EmitsSwtof;

    { Integer → Double/Single implicit assignment }
    procedure TestIntAssignDouble_EmitsSwtof;
    procedure TestInt64AssignDouble_EmitsSltof;
    procedure TestIntAssignSingle_EmitsSwtof;

    { Integer→float conversion on a CLASS-FIELD store target (not just a
      simple variable).  Regression: the field-store path emitted a bare
      integer store into the float slot. }
    procedure TestInt64AssignDoubleField_EmitsSltof;
    procedure TestIntAssignSingleField_EmitsSwtof;
    procedure TestInt64AssignDoubleFieldBare_EmitsSltof;

    { Mixed Single×Double arithmetic }
    procedure TestSingleMulDouble_PromotesSingleToDouble;
    procedure TestSingleAddSingle_EmitsSTypedOp;
    procedure TestSingleMulSingle_EmitsSTypedOp;
    procedure TestIntAddSingle_PromotesIntToSingle;
    procedure TestSingleCompare_EmitsSTypedCmp;
  end;

implementation

function TCodeGenTests.GenerateIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TCodeGenTests.GenerateNativeAsm(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenNative.Create();
  try
    CG.SetTarget(HostTarget());
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TCodeGenTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) >= 0;
end;

{ Data sections }

procedure TCodeGenTests.TestHelloWorld_HasStrLitData;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hello'') end.');
  AssertTrue('Has str data',
    IRContains(IR, 'data $__s0'));
  AssertTrue('Contains Hello',
    IRContains(IR, '"Hello"'));
end;

procedure TCodeGenTests.TestHelloWorld_UsesSysWriteStr;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hello'') end.');
  AssertTrue('Calls _SysWriteStr',
    IRContains(IR, 'call $_SysWriteStr('));
end;

{ Main function structure }

procedure TCodeGenTests.TestOutput_HasMainFunction;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin end.');
  AssertTrue('Has export function $main',
    IRContains(IR, 'export function w $main('));
end;

procedure TCodeGenTests.TestOutput_HasRetZero;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin end.');
  AssertTrue('Has ret 0', IRContains(IR, 'ret 0'));
end;

{ main must call $_BlaiseInit so RTL units whose initialization sections do
  not otherwise run (archive units) get their one-time setup — e.g. the
  weak-reference table mutex.  See blaise_weak._BlaiseInit. }
procedure TCodeGenTests.TestMain_CallsBlaiseInit;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin end.');
  AssertTrue('main calls $_BlaiseInit',
    IRContains(IR, 'call $_BlaiseInit()'));
end;

{ The native backend must also emit the _BlaiseInit call (right after
  _SetArgs, which it must follow because _BlaiseInit clobbers the SysV arg
  registers).  Guards against a backend skew where only one backend wires
  up the RTL startup hook. }
procedure TCodeGenTests.TestMain_Native_CallsBlaiseInit;
var
  Asm_: string;
  Call: string;
begin
  Asm_ := GenerateNativeAsm('program P; begin end.');
  { GenerateNativeAsm targets the HOST, so the call mnemonic is the host's:
    x86-64 emits `callq _Sym`, arm64 `bl _Sym`.  Asserting one host's syntax
    made this fail on macOS arm64 for no reason — the invariant under test is
    that main calls both, in that order, and that holds on either.  Select the
    mnemonic from the host target rather than gating the test away, so arm64
    keeps the coverage. }
  if HostTarget().CPU = cpuArm64 then
    Call := 'bl '
  else
    Call := 'callq ';
  { The PREFIX follows the target OS, not the CPU.  These RTL routines are named
    _BlaiseInit / _SetArgs in Pascal, and on Darwin every symbol takes one more
    '_' (Apple's C prefix, uniform with QBE), so the label is __BlaiseInit
    there and _BlaiseInit on ELF. }
  if HostTarget().OS = osMacOS then
    Call := Call + '__'
  else
    Call := Call + '_';
  AssertTrue('native main calls _BlaiseInit',
    IRContains(Asm_, Call + 'BlaiseInit'));
  AssertTrue('native main calls _SetArgs',
    IRContains(Asm_, Call + 'SetArgs'));
  { _SetArgs must precede _BlaiseInit. }
  AssertTrue('_SetArgs precedes _BlaiseInit',
    Pos(Call + 'SetArgs', Asm_) < Pos(Call + 'BlaiseInit', Asm_));
end;

{ WriteLn }

procedure TCodeGenTests.TestWriteLn_NoArgs_CallsSysWriteNewline;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn() end.');
  AssertTrue('Calls _SysWriteNewline',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

procedure TCodeGenTests.TestWriteLn_StringLit_CallsSysWriteStr;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hi'') end.');
  AssertTrue('Calls _SysWriteStr with string pointer',
    IRContains(IR, 'call $_SysWriteStr(w 1,'));
  AssertTrue('Calls _SysWriteNewline for line ending',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

procedure TCodeGenTests.TestWriteLn_IntExpr_CallsSysWriteInt;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(42) end.');
  AssertTrue('Calls _SysWriteInt',
    IRContains(IR, 'call $_SysWriteInt(w 1,'));
  AssertTrue('Calls _SysWriteNewline for line ending',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

procedure TCodeGenTests.TestWriteLn_BoolExpr_CallsSysWriteBool;
var
  IR: string;
begin
  IR := GenerateIR('program P; var b: Boolean; begin b := True; WriteLn(b) end.');
  AssertTrue('Calls _SysWriteBool',
    IRContains(IR, 'call $_SysWriteBool(w 1,'));
end;

{ Variables and assignment }

procedure TCodeGenTests.TestIntVar_HasAlloc;
var
  IR: string;
begin
  IR := GenerateIR('program P; var x: Integer; begin end.');
  { Program-level var is a data-section global, not a stack alloc }
  AssertTrue('Has data decl for x',
    IRContains(IR, 'data $x'));
end;

procedure TCodeGenTests.TestAssignment_HasStorew;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 7 end.');
  AssertTrue('Has storew', IRContains(IR, 'storew'));
  { Program-level var n is a global: store goes to $n }
  AssertTrue('Stores to n', IRContains(IR, 'storew %_t0, $n'));
end;

procedure TCodeGenTests.TestAssignment_LoadAndStore;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var x, y: Integer; begin x := 1; y := x end.');
  { Program-level vars x, y are globals: load/store use $name }
  AssertTrue('Loads x', IRContains(IR, 'loadw $x'));
  AssertTrue('Stores y', IRContains(IR, '$y'));
end;

{ Arithmetic }

procedure TCodeGenTests.TestAdd_EmitsAddInstruction;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 3 + 4 end.');
  AssertTrue('Has add', IRContains(IR, '=w add'));
end;

procedure TCodeGenTests.TestMul_EmitsMulInstruction;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 2 * 5 end.');
  AssertTrue('Has mul', IRContains(IR, '=w mul'));
end;

{ Header comment }

procedure TCodeGenTests.TestOutput_HasSourceComment;
var
  IR: string;
begin
  IR := GenerateIR('program MyProg; begin end.');
  AssertTrue('Has source comment',
    IRContains(IR, '# Generated by Blaise Compiler'));
end;

{ String equality }

procedure TCodeGenTests.TestStringEq_EmitsStringEquals;
var
  IR: string;
begin
  IR := GenerateIR('''
    program P;
    var S1, S2: string; B: Boolean;
    begin
      B := S1 = S2
    end.
    ''');
  AssertTrue('Uses _StringEquals', IRContains(IR, '$_StringEquals'));
end;

procedure TCodeGenTests.TestStringNe_EmitsStringEqualsNegated;
var
  IR: string;
begin
  IR := GenerateIR('''
    program P;
    var S1, S2: string; B: Boolean;
    begin
      B := S1 <> S2
    end.
    ''');
  AssertTrue('Uses _StringEquals for <>', IRContains(IR, '$_StringEquals'));
end;

procedure TCodeGenTests.TestStringEq_SemanticCompiles;
var
  IR: string;
begin
  IR := GenerateIR('''
    program P;
    function Same(A, B: string): Boolean;
    begin
      Result := A = B
    end;
    var B: Boolean;
    begin
      B := Same('hello', 'world')
    end.
    ''');
  AssertTrue('Compiles', Length(IR) > 0);
  AssertTrue('Uses _StringEquals', IRContains(IR, '$_StringEquals'));
end;

{ True / False built-in constants }

procedure TCodeGenTests.TestTrue_EmitsCopyOne;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := True end.');
  AssertTrue('True emits copy 1', IRContains(IR, 'copy 1'));
end;

procedure TCodeGenTests.TestFalse_EmitsCopyZero;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := False end.');
  AssertTrue('False emits copy 0', IRContains(IR, 'copy 0'));
end;

procedure TCodeGenTests.TestTrue_AssignToBoolVar;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := True end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
end;

procedure TCodeGenTests.TestFalse_AssignToBoolVar;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := False end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
end;

procedure TCodeGenTests.TestTrue_InIfCondition;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var N: Integer; begin if True then N := 1 end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
  AssertTrue('Has conditional branch', IRContains(IR, 'jnz'));
end;

procedure TCodeGenTests.TestBoolFunc_ReturnTrue;
var
  IR: string;
begin
  IR := GenerateIR('''
    program P;
    function IsOK: Boolean;
    begin
      Result := True
    end;
    var B: Boolean;
    begin
      B := IsOK()
    end.
    ''');
  AssertTrue('IsOK function emitted', IRContains(IR, '$IsOK'));
  AssertTrue('True emits copy 1', IRContains(IR, 'copy 1'));
end;

procedure TCodeGenTests.TestResult_LowercaseAssign_CompilesOK;
var
  IR: string;
begin
  { 'result' (lowercase) must resolve to the same slot as 'Result' and
    produce valid QBE — regression test for the case-normalisation bug
    reported in https://github.com/graemeg/blaise/discussions/15 }
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'function MyAdd(X, Y: Integer): Integer;'      + LineEnding +
    'begin'                                        + LineEnding +
    '  result := X + Y'                            + LineEnding +
    'end;'                                         + LineEnding +
    'var Z: Integer;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  Z := MyAdd(2, 3)'                           + LineEnding +
    'end.');
  AssertTrue('storew to Result slot (canonical casing)',
    IRContains(IR, 'storew %_t'));
  AssertFalse('no mis-cased %_var_result slot',
    IRContains(IR, '%_var_result ='));
end;

procedure TCodeGenTests.TestIdent_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  { Reading a variable with wrong casing must use the declared slot name }
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'var N: Integer;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  n := 42'                                    + LineEnding +
    'end.');
  AssertTrue('canonical $N global used', IRContains(IR, '$N'));
  AssertFalse('no mis-cased $n global', IRContains(IR, '$n ='));
end;

procedure TCodeGenTests.TestFieldAccess_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                     + LineEnding +
    'type'                                           + LineEnding +
    '  TFoo = class'                                 + LineEnding +
    '    FVal: Integer;'                             + LineEnding +
    '    function GetVal: Integer;'                  + LineEnding +
    '  end;'                                         + LineEnding +
    'function TFoo.GetVal: Integer;'                 + LineEnding +
    'begin Result := Self.FVal end;'                 + LineEnding +
    'var MyObj: TFoo;'                               + LineEnding +
    'begin'                                          + LineEnding +
    '  MyObj := TFoo.Create();'                        + LineEnding +
    '  WriteLn(myobj.GetVal())'                        + LineEnding +
    'end.');
  AssertTrue('definition uses declared $MyObj',
    Pos('data $MyObj', IR) >= 0);
  AssertTrue('reference uses declared $MyObj',
    Pos('loadl $MyObj', IR) >= 0);
  AssertFalse('no mis-cased $myobj reference',
    Pos('$myobj', IR) >= 0);
end;

procedure TCodeGenTests.TestForLoop_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                     + LineEnding +
    'var Counter: Integer;'                          + LineEnding +
    'begin'                                          + LineEnding +
    '  for counter := 1 to 5 do'                    + LineEnding +
    '    WriteLn(counter)'                           + LineEnding +
    'end.');
  AssertTrue('definition uses declared $Counter',
    Pos('data $Counter', IR) >= 0);
  AssertFalse('no mis-cased $counter in IR',
    Pos('$counter', IR) >= 0);
end;

procedure TCodeGenTests.TestFuncCall_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                     + LineEnding +
    'procedure DoStuff(X: Integer);'                 + LineEnding +
    'begin WriteLn(X) end;'                          + LineEnding +
    'begin'                                          + LineEnding +
    '  dostuff(3)'                                   + LineEnding +
    'end.');
  AssertTrue('proc def uses declared name DoStuff',
    Pos('function $DoStuff', IR) >= 0);
  AssertTrue('call uses declared name DoStuff',
    Pos('call $DoStuff', IR) >= 0);
  AssertFalse('no mis-cased $dostuff in IR',
    Pos('$dostuff', IR) >= 0);
end;

procedure TCodeGenTests.TestAssign_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                     + LineEnding +
    'type'                                           + LineEnding +
    '  TRec = record'                                + LineEnding +
    '    Val: Integer;'                              + LineEnding +
    '  end;'                                         + LineEnding +
    'var MyRec: TRec;'                               + LineEnding +
    'begin'                                          + LineEnding +
    '  myrec.Val := 42'                              + LineEnding +
    'end.');
  AssertTrue('definition uses declared $MyRec',
    Pos('data $MyRec', IR) >= 0);
  AssertFalse('no mis-cased $myrec in IR',
    Pos('$myrec', IR) >= 0);
end;

procedure TCodeGenTests.TestMethodCallObj_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                     + LineEnding +
    'type'                                           + LineEnding +
    '  TFoo = class'                                 + LineEnding +
    '    procedure DoIt;'                            + LineEnding +
    '  end;'                                         + LineEnding +
    'procedure TFoo.DoIt();'                           + LineEnding +
    'begin end;'                                     + LineEnding +
    'var Obj: TFoo;'                                 + LineEnding +
    'begin'                                          + LineEnding +
    '  Obj := TFoo.Create();'                          + LineEnding +
    '  obj.DoIt()'                                     + LineEnding +
    'end.');
  AssertTrue('definition uses declared $Obj',
    Pos('data $Obj', IR) >= 0);
  AssertFalse('no mis-cased $obj in IR (lowercase)',
    Pos('$obj', IR) >= 0);
end;

procedure TCodeGenTests.TestInt64MulDouble_EmitsSltof;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                       + LineEnding +
    'var M: Int64; D: Double;'         + LineEnding +
    'begin'                            + LineEnding +
    '  M := 123456789012345;'          + LineEnding +
    '  D := M * 1.0'                   + LineEnding +
    'end.');
  AssertTrue('should emit sltof for Int64→Double',
    IRContains(IR, 'sltof'));
  AssertFalse('should not use swtof for Int64',
    IRContains(IR, 'swtof'));
end;

procedure TCodeGenTests.TestIntMulDouble_EmitsSwtof;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                       + LineEnding +
    'var N: Integer; D: Double;'       + LineEnding +
    'begin'                            + LineEnding +
    '  N := 42;'                       + LineEnding +
    '  D := N * 1.0'                   + LineEnding +
    'end.');
  AssertTrue('should emit swtof for Integer→Double',
    IRContains(IR, 'swtof'));
end;

procedure TCodeGenTests.TestIntAssignDouble_EmitsSwtof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var D: Double;
    begin
      D := 4345
    end.
    ''');
  AssertTrue('should emit swtof for Integer literal→Double',
    IRContains(IR, 'swtof'));
end;

procedure TCodeGenTests.TestInt64AssignDouble_EmitsSltof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var N: Int64; D: Double;
    begin
      N := 100;
      D := N
    end.
    ''');
  AssertTrue('should emit sltof for Int64 var→Double',
    IRContains(IR, 'sltof'));
end;

procedure TCodeGenTests.TestIntAssignSingle_EmitsSwtof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var S: Single;
    begin
      S := 4345
    end.
    ''');
  AssertTrue('should emit swtof for Integer literal→Single',
    IRContains(IR, 'swtof'));
end;

procedure TCodeGenTests.TestInt64AssignDoubleField_EmitsSltof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    type TFoo = class
      FD: Double;
      procedure SetIt(AValue: Int64);
      begin Self.FD := AValue end;
    end;
    var F: TFoo;
    begin
      F := TFoo.Create()
    end.
    ''');
  AssertTrue('Int64→Double field store should emit sltof',
    IRContains(IR, 'sltof'));
  AssertFalse('Int64→Double field store must not bare-store the integer',
    IRContains(IR, 'storel %_t2, %_t1'));
end;

procedure TCodeGenTests.TestIntAssignSingleField_EmitsSwtof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    type TFoo = class
      FS: Single;
      procedure SetIt(AValue: Integer);
      begin Self.FS := AValue end;
    end;
    var F: TFoo;
    begin
      F := TFoo.Create()
    end.
    ''');
  AssertTrue('Integer→Single field store should emit swtof',
    IRContains(IR, 'swtof'));
end;

procedure TCodeGenTests.TestInt64AssignDoubleFieldBare_EmitsSltof;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    type TFoo = class
      FD: Double;
      procedure SetIt(AValue: Int64);
      begin FD := AValue end;
    end;
    var F: TFoo;
    begin
      F := TFoo.Create()
    end.
    ''');
  AssertTrue('Int64→Double bare implicit-Self field store should emit sltof',
    IRContains(IR, 'sltof'));
end;

procedure TCodeGenTests.TestSingleMulDouble_PromotesSingleToDouble;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var S: Single; D: Double;
    begin
      D := S * 1.0
    end.
    ''');
  AssertTrue('should widen Single to Double via exts',
    IRContains(IR, 'exts'));
  AssertTrue('result should be =d mul',
    IRContains(IR, '=d mul'));
end;

procedure TCodeGenTests.TestSingleAddSingle_EmitsSTypedOp;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var A, B, C: Single;
    begin
      C := A + B
    end.
    ''');
  AssertTrue('Single+Single should emit =s add',
    IRContains(IR, '=s add'));
end;

procedure TCodeGenTests.TestSingleMulSingle_EmitsSTypedOp;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var A, B, C: Single;
    begin
      C := A * B
    end.
    ''');
  AssertTrue('Single*Single should emit =s mul',
    IRContains(IR, '=s mul'));
end;

procedure TCodeGenTests.TestIntAddSingle_PromotesIntToSingle;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var S, R: Single;
        N: Integer;
    begin
      R := S + N
    end.
    ''');
  AssertTrue('Int+Single result should be promoted to Double (=d)',
    IRContains(IR, '=d'));
end;

procedure TCodeGenTests.TestSingleCompare_EmitsSTypedCmp;
var IR: string;
begin
  IR := GenerateIR('''
    program P;
    var A, B: Single;
    begin
      if A < B then
        WriteLn('yes')
    end.
    ''');
  AssertTrue('Single<Single should emit clts (s-typed compare)',
    IRContains(IR, 'clts'));
end;

initialization
  RegisterTest(TCodeGenTests);

end.
