{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.caseenum;

{ Tests for case statements and enum types — required for self-hosting.
  The compiler source uses both throughout (TTokenKind, TTypeKind, etc.). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TCaseEnumTests = class(TTestCase)
  private
    procedure SemanticOK(const ASrc: string);
    procedure ParseOK(const ASrc: string);
    { Analyse ASrc; return the raised semantic-error message, or '' if none. }
    function SemanticErrText(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { case — parse                                                         }
    { ------------------------------------------------------------------ }
    procedure TestParse_Case_SimpleInteger;
    procedure TestParse_Case_WithElse;
    procedure TestParse_Case_MultipleValuesPerBranch;

    { ------------------------------------------------------------------ }
    { case — semantic                                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Case_IntegerSelector_OK;
    procedure TestSemantic_Case_MultipleValues_OK;

    { ------------------------------------------------------------------ }
    { case — codegen                                                       }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { enum — parse                                                         }
    { ------------------------------------------------------------------ }
    procedure TestParse_Enum_SimpleDefinition;
    procedure TestParse_Enum_ThreeMembers;

    { ------------------------------------------------------------------ }
    { enum — semantic                                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Enum_MembersResolveAsConstants;
    procedure TestSemantic_Enum_VariableAssignment_OK;
    procedure TestSemantic_Enum_CompareMembers_OK;

    { ------------------------------------------------------------------ }
    { enum — codegen                                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ScopedEnum_UnknownMemberRejected;
    procedure TestSemantic_ScopedEnum_SharedMemberCompiles;
    procedure TestSemantic_ScopedEnum_AssignmentDisambiguates;
    procedure TestSemantic_ScopedEnum_CaseDisambiguates;
    procedure TestSemantic_ScopedEnum_SetElementDisambiguates;
    procedure TestSemantic_ScopedEnum_AmbiguousBareRejected;
    procedure TestSemantic_ScopedEnum_UniqueBareResolves;
    procedure TestSemantic_ScopedEnum_CallArgDisambiguates;
    procedure TestSemantic_ScopedEnum_CallArgResolvesCleanly;
    procedure TestSemantic_ScopedEnum_FieldAssignDisambiguates;
    procedure TestSemantic_ScopedEnum_MethodArgDisambiguates;
    procedure TestSemantic_ScopedEnum_ForBoundsDisambiguate;

    { ------------------------------------------------------------------ }
    { enum + case integration                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { enum — explicit ordinal values                                       }
    { ------------------------------------------------------------------ }
    procedure TestParse_Enum_ExplicitOrdinals;
    procedure TestParse_Enum_PartialExplicitOrdinals;
    procedure TestParse_Enum_ExplicitNegativeOrdinal;
    procedure TestSemantic_Enum_ExplicitOrdinals_CorrectValues;

    { ------------------------------------------------------------------ }
    { case — string selector (Step 11f prerequisite)                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_CaseString_AcceptsStringSelector;
    procedure TestSemantic_CaseString_RejectsIntLabelOnStringSelector;
  end;

implementation

const
  SrcCaseSimple =
    '''
        program P;
        var N: Integer;
        begin
          N := 2;
          case N of
            1: WriteLn(1);
            2: WriteLn(2);
            3: WriteLn(3)
          end
        end.
        ''';

  SrcCaseWithElse =
    '''
        program P;
        var N: Integer;
        begin
          N := 5;
          case N of
            1: WriteLn(1);
            2: WriteLn(2)
          else
            WriteLn(99)
          end
        end.
        ''';

  SrcCaseMultiValue =
    '''
        program P;
        var N: Integer;
        begin
          N := 3;
          case N of
            1, 2: WriteLn(12);
            3, 4: WriteLn(34)
          end
        end.
        ''';

  SrcEnumSimple =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        begin
        end.
        ''';

  SrcEnumAssign =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        var D: TDir;
        begin
          D := dSouth
        end.
        ''';

  SrcEnumCompare =
    '''
        program P;
        type
          TDir = (dNorth, dSouth);
        var
          D: TDir;
          B: Boolean;
        begin
          D := dNorth;
          B := (D = dNorth)
        end.
        ''';

  SrcEnumInCase =
    '''
        program P;
        type
          TState = (sIdle, sRunning, sDone);
        var
          S: TState;
          N: Integer;
        begin
          S := sRunning;
          case S of
            sIdle:    N := 0;
            sRunning: N := 1;
            sDone:    N := 2
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.SemanticOK(const ASrc: string);
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

procedure TCaseEnumTests.ParseOK(const ASrc: string);
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

function TCaseEnumTests.SemanticErrText(const ASrc: string): string;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Result := '';
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Prog);
    except
      on E: Exception do Result := E.Message;
    end;
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ case — parse                                                         }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Case_SimpleInteger;
begin
  ParseOK(SrcCaseSimple);
end;

procedure TCaseEnumTests.TestParse_Case_WithElse;
begin
  ParseOK(SrcCaseWithElse);
end;

procedure TCaseEnumTests.TestParse_Case_MultipleValuesPerBranch;
begin
  ParseOK(SrcCaseMultiValue);
end;

{ ------------------------------------------------------------------ }
{ case — semantic                                                      }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_Case_IntegerSelector_OK;
begin
  SemanticOK(SrcCaseSimple);
end;

procedure TCaseEnumTests.TestSemantic_Case_MultipleValues_OK;
begin
  SemanticOK(SrcCaseMultiValue);
end;

{ ------------------------------------------------------------------ }
{ case — codegen                                                       }
{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }
{ enum — parse                                                         }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Enum_SimpleDefinition;
begin
  ParseOK(SrcEnumSimple);
end;

procedure TCaseEnumTests.TestParse_Enum_ThreeMembers;
begin
  ParseOK(SrcEnumAssign);
end;

{ ------------------------------------------------------------------ }
{ enum — semantic                                                      }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_Enum_MembersResolveAsConstants;
var
  Lex:    TLexer;
  Par:    TParser;
  SA:     TSemanticAnalyser;
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Lex  := TLexer.Create(SrcEnumAssign);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  { D := dSouth — the RHS should have tyEnum resolved type }
  Assign := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('dSouth resolves to enum type',
    Ord(tyEnum), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TCaseEnumTests.TestSemantic_Enum_VariableAssignment_OK;
begin
  SemanticOK(SrcEnumAssign);
end;

procedure TCaseEnumTests.TestSemantic_Enum_CompareMembers_OK;
begin
  SemanticOK(SrcEnumCompare);
end;

{ ------------------------------------------------------------------ }
{ enum — codegen                                                       }
{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }
{ enum + case integration                                              }
{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }
{ enum — explicit ordinal values                                       }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Enum_ExplicitOrdinals;
begin
  ParseOK(
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestParse_Enum_PartialExplicitOrdinals;
begin
  ParseOK(
    '''
        program P;
        type
          TCode = (A=100, B, C);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestParse_Enum_ExplicitNegativeOrdinal;
begin
  ParseOK(
    '''
        program P;
        type
          TOffset = (Before=-1, At=0, After=1);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestSemantic_Enum_ExplicitOrdinals_CorrectValues;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Assign: TAssignment;
begin
  { Running=20 — the RHS ConstValue should be 20, not 1 }
  Lex  := TLexer.Create(
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        var S: TStatus;
        begin
          S := Running
        end.
        ''');
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Assign := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('Running ordinal is 20', 20, TIdentExpr(Assign.Expr).ConstValue);
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ case — string selector                                               }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_CaseString_AcceptsStringSelector;
const
  Src =
    '''
        program P;
        var S: string; R: Integer;
        begin
          S := 'foo';
          case S of
            'bar': R := 1;
            'foo': R := 2
          else
            R := 99
          end
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_CaseString_RejectsIntLabelOnStringSelector;
const
  Src =
    '''
        program P;
        var S: string;
        begin
          S := 'foo';
          case S of
            1: S := 'one'
          end
        end.
        ''';
var
  Raised: Boolean;
begin
  Raised := False;
  try
    SemanticOK(Src);
  except
    on E: Exception do Raised := True;
  end;
  AssertTrue('integer literal label on string-typed selector rejected', Raised);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_UnknownMemberRejected;
const
  Src =
    '''
        program P;
        type TDir = (dN, dE, dS, dW);
        var x: Integer;
        begin
          x := Ord(TDir.dNope)
        end.
        ''';
var
  Raised: Boolean;
begin
  Raised := False;
  try
    SemanticOK(Src);
  except
    on E: Exception do Raised := True;
  end;
  AssertTrue('unknown enum member via TEnum.Member rejected', Raised);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_SharedMemberCompiles;
const
  { Two enums in one unit both declare 'Red'.  Members are no longer bare
    global symbols, so this is NOT a collision — each is reachable through its
    own type, and the program compiles cleanly. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        begin
          WriteLn(Ord(TColorA.Red));
          WriteLn(Ord(TColorB.Red))
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_AssignmentDisambiguates;
const
  { 'Red' belongs to both enums; the assignment target type selects which one,
    so BOTH assignments type-check (a fallback-only resolver would mis-type one). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        var
          a: TColorA;
          b: TColorB;
        begin
          a := Red;
          b := Red;
          WriteLn(Ord(a) + Ord(b))
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_CaseDisambiguates;
const
  { The case selector's type picks the enum for a bare, shared member label. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        var
          b: TColorB;
        begin
          b := Blue;
          case b of
            Red:  WriteLn(1);
            Blue: WriteLn(2)
          end
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_SetElementDisambiguates;
const
  { The set's element type picks the enum for a bare, shared member element. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        var
          s: set of TColorA;
        begin
          s := [Red, Green];
          if Red in s then WriteLn(1)
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_AmbiguousBareRejected;
const
  { A bare, context-free reference to a member shared by two enums cannot be
    resolved: it is rejected with an error that names the member and lists the
    enums that declare it. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        begin
          WriteLn(Ord(Red))
        end.
        ''';
var
  E: string;
begin
  E := SemanticErrText(Src);
  AssertTrue('the ambiguous bare member is rejected', E <> '');
  AssertTrue('error names the ambiguous member', Pos('''Red''', E) >= 0);
  AssertTrue('error names the first declaring enum',  Pos('TColorA', E) >= 0);
  AssertTrue('error names the second declaring enum', Pos('TColorB', E) >= 0);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_UniqueBareResolves;
const
  { A bare member unique across all enums needs no context and resolves
    cleanly with no error. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Cyan, Blue);
        begin
          WriteLn(Ord(Green))
        end.
        ''';
begin
  AssertEquals('unique bare member resolves with no error', '',
    SemanticErrText(Src));
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_CallArgDisambiguates;
const
  { 'Red' is shared; a bare member passed as a call argument is steered to the
    enum the routine expects at that position, so both calls type-check. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        procedure TakeA(c: TColorA);
        begin WriteLn(Ord(c)) end;
        procedure TakeB(c: TColorB);
        begin WriteLn(Ord(c)) end;
        begin
          TakeA(Red);
          TakeB(Red)
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_CallArgResolvesCleanly;
const
  { A shared member resolved by the call target's parameter type is NOT
    ambiguous — the hint pins it before bottom-up analysis, so no error. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        procedure TakeA(c: TColorA);
        begin WriteLn(Ord(c)) end;
        begin
          TakeA(Red)
        end.
        ''';
begin
  AssertEquals('call-arg hint resolves with no error', '',
    SemanticErrText(Src));
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_FieldAssignDisambiguates;
const
  { Assigning a bare shared member to a record field is disambiguated by the
    field's declared enum type — the same context that lets the compiler's own
    'Result.Kind := tkAs' resolve when tkAs is shared by two enums. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
          TRec = record c: TColorB; end;
        var r: TRec;
        begin
          r.c := Red;
          WriteLn(Ord(r.c))
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_MethodArgDisambiguates;
const
  { A bare shared member passed to a method argument is steered to the enum of
    the method's parameter, resolved by walking the receiver's class. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
          TFoo = class
            procedure TakeB(c: TColorB);
          end;
        procedure TFoo.TakeB(c: TColorB);
        begin WriteLn(Ord(c)) end;
        var f: TFoo;
        begin
          f := TFoo.Create();
          f.TakeB(Red);
          f.Free()
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_ScopedEnum_ForBoundsDisambiguate;
const
  { The loop variable's type picks the enum for bare, shared start/end bounds. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        var
          b: TColorB;
        begin
          for b := Red to Blue do
            WriteLn(Ord(b))
        end.
        ''';
begin
  SemanticOK(Src);
end;

initialization
  RegisterTest(TCaseEnumTests);

end.
