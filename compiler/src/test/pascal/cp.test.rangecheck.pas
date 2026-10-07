{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.rangecheck;

{ Compile-time range checking of CONSTANT values stored into a subrange or
  enum-typed destination (BUG-20260921-no-compile-time-range-check).

  Scope, as ruled: stores, arguments and initialisers only.  Explicit enum
  casts (TE(99)), for-loop bounds and case labels are deliberately NOT
  checked -- see docs/language-rationale.adoc.  An enum's valid range is
  MIN..MAX declared ordinal, so interior holes in an explicitly-numbered
  enum stay legal. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TRangeCheckTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function Accepts(const ASrc: string): Boolean;
    { Analyses ASrc and returns the semantic error message, or '' when the
      source analysed cleanly. }
    function SemanticErrMsg(const ASrc: string): string;
  published
    { ---------------------------------------------------------------- }
    { Integer subrange — must be REJECTED                              }
    { ---------------------------------------------------------------- }
    procedure TestAssign_AboveHigh_Raises;
    procedure TestAssign_BelowLow_Raises;
    procedure TestAssign_NamedConst_Raises;
    procedure TestAssign_FoldedExpr_Raises;
    procedure TestAssign_Negative_Raises;
    procedure TestResultAssign_Raises;
    procedure TestRecordField_Raises;
    procedure TestClassField_ImplicitSelf_Raises;
    procedure TestClassField_Qualified_Raises;
    procedure TestArrayElement_Raises;
    procedure TestValueArg_StandaloneProc_Raises;
    procedure TestValueArg_Method_Raises;
    procedure TestDefaultParamValue_Raises;
    procedure TestGlobalVarInitialiser_Raises;
    procedure TestErrorNamesValueTypeAndRange;

    { ---------------------------------------------------------------- }
    { Integer subrange — must still be ACCEPTED                        }
    { ---------------------------------------------------------------- }
    procedure TestAssign_InRange_Accepted;
    procedure TestAssign_BothBoundaries_Accepted;
    procedure TestVariableValue_NotDiagnosed;
    procedure TestHighExpr_NotDiagnosed;

    { ---------------------------------------------------------------- }
    { Enum destinations — MIN..MAX ordinal, holes legal                }
    { ---------------------------------------------------------------- }
    procedure TestEnumSubrange_MemberBelowLow_Raises;
    procedure TestEnumSubrange_MemberInRange_Accepted;
    procedure TestEnum_ExplicitOrdinal_InteriorHole_Accepted;
    procedure TestEnum_ExplicitOrdinal_BelowMin_Raises;
    procedure TestEnum_ExplicitOrdinal_AboveMax_Raises;

    { ---------------------------------------------------------------- }
    { Deliberately OUT of scope — must NOT be diagnosed                }
    { ---------------------------------------------------------------- }
    procedure TestEnumCast_OutOfRange_NotDiagnosed;
    procedure TestForLoopBound_NotDiagnosed;
    procedure TestCaseLabel_NotDiagnosed;

    { ---------------------------------------------------------------- }
    { Enum-member name shadowing — the 20caf3aa lesson                 }
    { ---------------------------------------------------------------- }
    procedure TestShadowingGlobalVar_NotFolded;
    procedure TestShadowingParam_NotFolded;
    procedure TestShadowingField_NotFolded;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TRangeCheckTests.AnalyseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  Result := nil;
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

{ The program passes the semantic pass (a rejection raises, failing the
  test with the diagnostic). }
function TRangeCheckTests.Accepts(const ASrc: string): Boolean;
begin
  AnalyseSrc(ASrc).Free();
  Result := True;
end;

function TRangeCheckTests.SemanticErrMsg(const ASrc: string): string;
var
  Pr: TProgram;
begin
  Result := '';
  Pr := nil;
  try
    try
      Pr := AnalyseSrc(ASrc);
    except
      on E: Exception do Result := E.Message;
    end;
  finally
    Pr.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Integer subrange — rejected                                         }
{ ------------------------------------------------------------------ }

procedure TRangeCheckTests.TestAssign_AboveHigh_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 6 end.
    ''');
  AssertTrue('v := 6 on 1..5 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestAssign_BelowLow_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 0 end.
    ''');
  AssertTrue('v := 0 on 1..5 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestAssign_NamedConst_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    const K = 9;
    var v: TStd;
    begin v := K end.
    ''');
  AssertTrue('v := K with K=9 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestAssign_FoldedExpr_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 2 + 4 end.
    ''');
  AssertTrue('v := 2+4 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestAssign_Negative_Raises;
var Msg: string;
begin
  { -3 parses as BinaryExpr(0 - 3), so the fold must handle it. }
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := -3 end.
    ''');
  AssertTrue('v := -3 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestResultAssign_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    function F(): TStd;
    begin Result := 7 end;
    begin F() end.
    ''');
  AssertTrue('Result := 7 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestRecordField_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TStd = 1..5;
      TRec = record F: TStd; end;
    var r: TRec;
    begin r.F := 10 end.
    ''');
  AssertTrue('r.F := 10 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestClassField_ImplicitSelf_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TStd = 1..5;
      TC = class
        FV: TStd;
        procedure Go();
      end;
    procedure TC.Go();
    begin FV := 11 end;
    begin end.
    ''');
  AssertTrue('implicit-Self FV := 11 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestClassField_Qualified_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TStd = 1..5;
      TC = class
        FV: TStd;
      end;
    var c: TC;
    begin c := TC.Create(); c.FV := 14 end.
    ''');
  AssertTrue('c.FV := 14 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestArrayElement_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var a: array[0..3] of TStd;
    begin a[0] := 13 end.
    ''');
  AssertTrue('a[0] := 13 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestValueArg_StandaloneProc_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    procedure Q(a: TStd);
    begin WriteLn(a) end;
    begin Q(8) end.
    ''');
  AssertTrue('Q(8) must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestValueArg_Method_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type
      TStd = 1..5;
      TC = class
        procedure Go(a: TStd);
      end;
    procedure TC.Go(a: TStd);
    begin WriteLn(a) end;
    var c: TC;
    begin c := TC.Create(); c.Go(9) end.
    ''');
  AssertTrue('c.Go(9) must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestDefaultParamValue_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    procedure Q(a: TStd = 12);
    begin WriteLn(a) end;
    begin Q() end.
    ''');
  AssertTrue('default value 12 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestGlobalVarInitialiser_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd = 8;
    begin WriteLn(v) end.
    ''');
  AssertTrue('var v: TStd = 8 must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestErrorNamesValueTypeAndRange;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 42 end.
    ''');
  AssertTrue('names the value 42, got: ' + Msg, Pos('42', Msg) >= 0);
  AssertTrue('names the type TStd, got: ' + Msg, Pos('TStd', Msg) >= 0);
  AssertTrue('names the range 1..5, got: ' + Msg, Pos('1..5', Msg) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Integer subrange — accepted                                         }
{ ------------------------------------------------------------------ }

procedure TRangeCheckTests.TestAssign_InRange_Accepted;
begin
  AssertTrue('in-range constant still compiles', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 3 end.
    '''));
end;

procedure TRangeCheckTests.TestAssign_BothBoundaries_Accepted;
begin
  { Both bounds are INCLUSIVE — the off-by-one guard. }
  AssertTrue('both boundaries accepted', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := 1; v := 5 end.
    '''));
end;

procedure TRangeCheckTests.TestVariableValue_NotDiagnosed;
begin
  { Not a compile-time fact — must not be rejected even though the value
    is obviously out of range at runtime. }
  AssertTrue('variable value is not diagnosed', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd; i: Integer;
    begin i := 99; v := i end.
    '''));
end;

procedure TRangeCheckTests.TestHighExpr_NotDiagnosed;
begin
  { High()/Low() are not folded by the constant fold, so this is a
    conservative miss rather than a false positive. }
  AssertTrue('High(TStd)+1 is not diagnosed', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin v := High(TStd) + 1 end.
    '''));
end;

{ ------------------------------------------------------------------ }
{ Enum destinations                                                   }
{ ------------------------------------------------------------------ }

procedure TRangeCheckTests.TestEnumSubrange_MemberBelowLow_Raises;
var Msg: string;
begin
  { eA has ordinal 0; TMid covers 1..2. }
  Msg := SemanticErrMsg('''
    program P;
    type
      TE = (eA, eB, eC);
      TMid = eB..eC;
    var m: TMid;
    begin m := eA end.
    ''');
  AssertTrue('m := eA on eB..eC must be rejected, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestEnumSubrange_MemberInRange_Accepted;
begin
  AssertTrue('in-range enum members accepted', Accepts('''
    program P;
    type
      TE = (eA, eB, eC);
      TMid = eB..eC;
    var m: TMid;
    begin m := eB; m := eC end.
    '''));
end;

procedure TRangeCheckTests.TestEnum_ExplicitOrdinal_InteriorHole_Accepted;
begin
  { RULED: an enum's range is MIN..MAX declared ordinal, so 7 — which no
    member declares — is legal for (xA=5, xB=10).  This matches Delphi/FPC
    and converges with BUG-20260922-explicit-ordinal-enum-array-bounds. }
  AssertTrue('interior hole 7 accepted for (xA=5, xB=10)', Accepts('''
    program P;
    type TX = (xA = 5, xB = 10);
    var x: TX;
    begin x := 7 end.
    '''));
end;

procedure TRangeCheckTests.TestEnum_ExplicitOrdinal_BelowMin_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TX = (xA = 5, xB = 10);
    var x: TX;
    begin x := 4 end.
    ''');
  AssertTrue('4 is below min ordinal 5, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

procedure TRangeCheckTests.TestEnum_ExplicitOrdinal_AboveMax_Raises;
var Msg: string;
begin
  Msg := SemanticErrMsg('''
    program P;
    type TX = (xA = 5, xB = 10);
    var x: TX;
    begin x := 11 end.
    ''');
  AssertTrue('11 is above max ordinal 10, got: ' + Msg,
    Pos('out of range', Msg) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Deliberately out of scope                                           }
{ ------------------------------------------------------------------ }

procedure TRangeCheckTests.TestEnumCast_OutOfRange_NotDiagnosed;
begin
  { RULED out of scope: an explicit cast is the programmer overriding the
    type system on purpose, and TE(-1) is a known sentinel idiom. }
  AssertTrue('explicit enum cast is not diagnosed', Accepts('''
    program P;
    type TE = (eA, eB, eC);
    var x: TE;
    begin x := TE(99) end.
    '''));
end;

procedure TRangeCheckTests.TestForLoopBound_NotDiagnosed;
begin
  { RULED out of scope. }
  AssertTrue('for-loop bounds are not diagnosed', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin for v := 1 to 5 do WriteLn(v) end.
    '''));
end;

procedure TRangeCheckTests.TestCaseLabel_NotDiagnosed;
begin
  { RULED out of scope: an unreachable label, not a bad store. }
  AssertTrue('case labels are not diagnosed', Accepts('''
    program P;
    type TStd = 1..5;
    var v: TStd;
    begin
      v := 1;
      case v of
        7: WriteLn('seven');
      else
        WriteLn('other')
      end
    end.
    '''));
end;

{ ------------------------------------------------------------------ }
{ Enum-member name shadowing (the 20caf3aa lesson)                    }
{ ------------------------------------------------------------------ }

procedure TRangeCheckTests.TestShadowingGlobalVar_NotFolded;
begin
  { 'eB' here is an Integer variable, not the enum member — it is not a
    constant at all and must not be folded to its ordinal. }
  AssertTrue('enum-shadowing global var is not folded', Accepts('''
    program P;
    type
      TE = (eA, eB, eC);
      TMid = eB..eC;
    var m: TMid; eB: Integer;
    begin eB := 2; m := eB end.
    '''));
end;

procedure TRangeCheckTests.TestShadowingParam_NotFolded;
begin
  AssertTrue('enum-shadowing parameter is not folded', Accepts('''
    program P;
    type
      TE = (eA, eB, eC);
      TMid = eB..eC;
    var m: TMid;
    procedure Q(eA: Integer);
    begin m := eA end;
    begin Q(2) end.
    '''));
end;

procedure TRangeCheckTests.TestShadowingField_NotFolded;
begin
  { A class FIELD is not in the symbol table, so a lookup-based guard would
    still mis-fold this — only the IsConstant annotation gets it right. }
  AssertTrue('enum-shadowing class field is not folded', Accepts('''
    program P;
    type
      TE = (eA, eB, eC);
      TMid = eB..eC;
      TC = class
        eA: Integer;
        FM: TMid;
        procedure Go();
      end;
    procedure TC.Go();
    begin eA := 2; FM := eA end;
    begin end.
    '''));
end;

initialization
  RegisterTest(TRangeCheckTests);

end.
