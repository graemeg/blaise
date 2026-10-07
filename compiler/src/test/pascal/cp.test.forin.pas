{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.forin;

{ Tests for for..in loop: class-based enumerators, static array, dynamic array, string, and set iteration. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TForInTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
    { Analyse ASrc and return the concatenated semantic warnings (one per line).
      Used to assert the BUG-001 for-in write diagnostics fire (or don't). }
    function AnalyseWarnings(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_ForIn_IsTForInStmt;
    procedure TestParse_ForIn_VarName;
    procedure TestParse_ForIn_CollExprIsIdent;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForIn_Valid_OK;
    procedure TestSemantic_ForIn_NoGetEnumerator_RaisesError;
    procedure TestSemantic_ForIn_MoveNextNotBoolean_RaisesError;
    procedure TestSemantic_ForIn_NoCurrent_RaisesError;
    procedure TestSemantic_ForIn_VarTypeMismatch_RaisesError;
    procedure TestSemantic_ForIn_CollNotClass_RaisesError;

    { ------------------------------------------------------------------ }
    { BUG-001 — writing a for-in loop variable is diagnosed              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ForIn_AssignLoopVar_Warns;
    procedure TestSemantic_ForIn_RecordFieldWrite_Warns;
    procedure TestSemantic_ForIn_ClassFieldWrite_NoWarn;
    procedure TestSemantic_ForIn_ReadOnly_NoWarn;
    procedure TestSemantic_IndexedFor_ElementWrite_NoWarn;
    procedure TestSemantic_ForIn_VarParamArg_Warns;
    procedure TestSemantic_ForIn_IncLoopVar_Warns;
    procedure TestSemantic_ForIn_ValueParamArg_NoWarn;
    procedure TestSemantic_ForIn_NestedRecordFieldWrite_Warns;
    procedure TestSemantic_ForIn_ClassNestedRecordWrite_NoWarn;

    { ------------------------------------------------------------------ }
    { Codegen — class enumerator                                           }
    { ------------------------------------------------------------------ }
    { A record-typed Current must sret straight into the loop variable
      (regression for the record-property-read heap corruption). }

    { ------------------------------------------------------------------ }
    { Semantic — static array                                              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ArrayForIn_Valid_OK;
    procedure TestSemantic_ArrayForIn_VarTypeMismatch_RaisesError;
    procedure TestSemantic_ArrayForIn_NonZeroBased_OK;

    { ------------------------------------------------------------------ }
    { Codegen — static array                                               }
    { ------------------------------------------------------------------ }
    { Issue #169: a record loop variable is copied by value (managed field ARC),
      not truncated to a scalar load. }

    { ------------------------------------------------------------------ }
    { Semantic — set                                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SetForIn_Valid_OK;
    procedure TestSemantic_SetForIn_VarTypeMismatch_RaisesError;
    procedure TestSemantic_SetForIn_NonSetCollNotAllowed;

    { ------------------------------------------------------------------ }
    { Codegen — set                                                        }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Semantic — dynamic array                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_DynArrayForIn_Valid_OK;
    procedure TestSemantic_DynArrayForIn_VarTypeMismatch_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen — dynamic array                                              }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Semantic — string                                                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StringForIn_ByteVar_OK;
    procedure TestSemantic_StringForIn_IntVar_IsCodePointIter;
    procedure TestSemantic_StringForIn_NonOrdinalVar_RaisesError;
    procedure TestSemantic_StringForIn_WordVar_RaisesError;
    procedure TestSemantic_StringForIn_SmallIntVar_RaisesError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TForInTests.ParseSrc(const ASrc: string): TProgram;
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

function TForInTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TForInTests.AnalyseWarnings(const ASrc: string): string;
var
  Prog: TProgram;
  A:    TSemanticAnalyser;
begin
  Prog := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Prog);
    Result := A.GetWarnings().Text;
  finally
    A.Free();
    Prog.Free();
  end;
end;

procedure TForInTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source — minimal enumerator+collection pair                  }
{ ------------------------------------------------------------------ }

const
  SrcEnumTypes =
    '''
        type
          TMyEnum = class
            FCurrent: Integer;
            function MoveNext: Boolean;
            function GetCurrent: Integer;
            property Current: Integer read GetCurrent;
          end;
          TMyCol = class
            function GetEnumerator: TMyEnum;
          end;
        function TMyEnum.MoveNext: Boolean;
        begin
          Result := False;
        end;
        function TMyEnum.GetCurrent: Integer;
        begin
          Result := FCurrent;
        end;
        function TMyCol.GetEnumerator: TMyEnum;
        begin
          Result := nil;
        end;
        ''';

  SrcForIn =
    'program P;' + #10 +
    SrcEnumTypes + #10 +
    '''
        var
          Col: TMyCol;
          X:   Integer;
        begin
          for X in Col do
            X := X + 1
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestParse_ForIn_IsTForInStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcForIn);
  try
    AssertTrue('stmt is TForInStmt',
      Prog.Block.Stmts[0] is TForInStmt);
  finally
    Prog.Free();
  end;
end;

procedure TForInTests.TestParse_ForIn_VarName;
var Prog: TProgram; FS: TForInStmt;
begin
  Prog := ParseSrc(SrcForIn);
  try
    FS := TForInStmt(Prog.Block.Stmts[0]);
    AssertEquals('loop var is X', 'X', FS.VarName);
  finally
    Prog.Free();
  end;
end;

procedure TForInTests.TestParse_ForIn_CollExprIsIdent;
var Prog: TProgram; FS: TForInStmt;
begin
  Prog := ParseSrc(SrcForIn);
  try
    FS := TForInStmt(Prog.Block.Stmts[0]);
    AssertTrue('collection is TIdentExpr', FS.CollExpr is TIdentExpr);
    AssertEquals('collection name is Col', 'Col',
      TIdentExpr(FS.CollExpr).Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_ForIn_Valid_OK;
begin
  AnalyseSrc(SrcForIn).Free();
end;

procedure TForInTests.TestSemantic_ForIn_NoGetEnumerator_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TBadCol = class
            FCount: Integer;
          end;
        var
          Col: TBadCol;
          X:   Integer;
        begin
          for X in Col do
            X := X + 1
        end.
        ''');
end;

procedure TForInTests.TestSemantic_ForIn_MoveNextNotBoolean_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TBadEnum = class
            function MoveNext: Integer;
            function GetCurrent: Integer;
            property Current: Integer read GetCurrent;
          end;
          TBadCol = class
            function GetEnumerator: TBadEnum;
          end;
        var
          Col: TBadCol;
          X:   Integer;
        begin
          for X in Col do
            X := X + 1
        end.
        ''');
end;

procedure TForInTests.TestSemantic_ForIn_NoCurrent_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TBadEnum = class
            function MoveNext: Boolean;
          end;
          TBadCol = class
            function GetEnumerator: TBadEnum;
          end;
        var
          Col: TBadCol;
          X:   Integer;
        begin
          for X in Col do
            X := X + 1
        end.
        ''');
end;

procedure TForInTests.TestSemantic_ForIn_VarTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;' + #10 +
    SrcEnumTypes + #10 +
    '''
        var
          Col: TMyCol;
          X:   string;
        begin
          for X in Col do
            X := X
        end.
        ''');
end;

procedure TForInTests.TestSemantic_ForIn_CollNotClass_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          X: Integer;
        begin
          for X in X do
            X := X + 1
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ BUG-001 — writing a for-in loop variable is diagnosed              }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_ForIn_AssignLoopVar_Warns;
var W: string;
begin
  W := AnalyseWarnings(
    '''
        program P;
        var
          A: array[0..2] of Integer;
          R: Integer;
        begin
          A[0] := 1;
          for R in A do
            R := 99
        end.
        ''');
  AssertTrue('assigning a for-in loop variable must warn',
    Pos('for-in loop variable', W) > 0);
end;

procedure TForInTests.TestSemantic_ForIn_RecordFieldWrite_Warns;
var W: string;
begin
  W := AnalyseWarnings(
    '''
        program P;
        type
          TRec = record N: Integer; end;
        var
          A: array[0..2] of TRec;
          R: TRec;
        begin
          for R in A do
            R.N := 7
        end.
        ''');
  AssertTrue('writing a field of a record for-in loop variable must warn',
    Pos('is discarded', W) > 0);
end;

procedure TForInTests.TestSemantic_ForIn_ClassFieldWrite_NoWarn;
var W: string;
begin
  { A for-in over class references binds the loop variable to the live object,
    so 'T.Field := x' legitimately mutates it — must NOT warn. }
  W := AnalyseWarnings(
    '''
        program P;
        type
          TThing = class
            Value: Integer;
          end;
        var
          A: array[0..1] of TThing;
          T: TThing;
        begin
          A[0] := TThing.Create();
          A[1] := TThing.Create();
          for T in A do
            T.Value := 42
        end.
        ''');
  AssertEquals('class for-in field write must not warn', '', Trim(W));
end;

procedure TForInTests.TestSemantic_ForIn_ReadOnly_NoWarn;
var W: string;
begin
  W := AnalyseWarnings(
    '''
        program P;
        var
          A: array[0..2] of Integer;
          R: Integer;
          S: Integer;
        begin
          S := 0;
          for R in A do
            S := S + R
        end.
        ''');
  AssertEquals('read-only for-in use must not warn', '', Trim(W));
end;

procedure TForInTests.TestSemantic_IndexedFor_ElementWrite_NoWarn;
var W: string;
begin
  { An indexed for loop writing A[I] is the correct way to mutate — no warning. }
  W := AnalyseWarnings(
    '''
        program P;
        type
          TRec = record N: Integer; end;
        var
          A: array[0..1] of TRec;
          I: Integer;
        begin
          for I := 0 to 1 do
            A[I].N := I
        end.
        ''');
  AssertEquals('indexed-for element write must not warn', '', Trim(W));
end;

procedure TForInTests.TestSemantic_ForIn_VarParamArg_Warns;
var W: string;
begin
  { BUG-001, by-ref arm: the callee mutates the per-iteration copy through
    the var reference — the change never reaches the collection element. }
  W := AnalyseWarnings(
    '''
        program P;
        var
          A: array[0..2] of Integer;
          R: Integer;

        procedure Bump(var X: Integer);
        begin
          X := X + 1
        end;

        begin
          for R in A do
            Bump(R)
        end.
        ''');
  AssertTrue('passing a for-in loop variable to a var parameter must warn',
    Pos('for-in loop variable', W) > 0);
end;

procedure TForInTests.TestSemantic_ForIn_IncLoopVar_Warns;
var W: string;
begin
  W := AnalyseWarnings(
    '''
        program P;
        var
          A: array[0..2] of Integer;
          R: Integer;
        begin
          for R in A do
            Inc(R)
        end.
        ''');
  AssertTrue('Inc on a for-in loop variable must warn',
    Pos('for-in loop variable', W) > 0);
end;

procedure TForInTests.TestSemantic_ForIn_ValueParamArg_NoWarn;
var W: string;
begin
  { Passing the loop variable by VALUE is a read — must NOT warn. }
  W := AnalyseWarnings(
    '''
        program P;
        var
          A: array[0..2] of Integer;
          R: Integer;

        procedure Show(X: Integer);
        begin
          WriteLn(X)
        end;

        begin
          for R in A do
            Show(R)
        end.
        ''');
  AssertEquals('value-param use of a for-in loop variable must not warn',
    '', Trim(W));
end;

procedure TForInTests.TestSemantic_ForIn_NestedRecordFieldWrite_Warns;
var W: string;
begin
  { Deep path: every link from the loop variable to the receiver is a value
    record, so the write lands in the per-iteration copy — must warn. }
  W := AnalyseWarnings(
    '''
        program P;
        type
          TInner = record N: Integer; end;
          TOuter = record Inner: TInner; end;
        var
          A: array[0..1] of TOuter;
          R: TOuter;
        begin
          for R in A do
            R.Inner.N := 7
        end.
        ''');
  AssertTrue('nested record field write through a for-in loop variable must warn',
    Pos('is discarded', W) > 0);
end;

procedure TForInTests.TestSemantic_ForIn_ClassNestedRecordWrite_NoWarn;
var W: string;
begin
  { The loop variable is a class reference: the embedded record lives in the
    live heap object, so the write DOES mutate it — must NOT warn. }
  W := AnalyseWarnings(
    '''
        program P;
        type
          TInner = record N: Integer; end;
          TThing = class
            Inner: TInner;
          end;
        var
          A: array[0..0] of TThing;
          T: TThing;
        begin
          A[0] := TThing.Create();
          for T in A do
            T.Inner.N := 7
        end.
        ''');
  AssertEquals('record field write through a class for-in loop variable must not warn',
    '', Trim(W));
end;

{ ------------------------------------------------------------------ }
{ Shared sources — static array                                        }
{ ------------------------------------------------------------------ }

const
  SrcArrayForIn =
    '''
        program P;
        var
          Arr: array[0..4] of Integer;
          X:   Integer;
        begin
          for X in Arr do
            X := X + 1
        end.
        ''';

  SrcArrayForInNonZero =
    '''
        program P;
        var
          Arr: array[3..7] of Integer;
          X:   Integer;
        begin
          for X in Arr do
            X := X + 1
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests — static array                                        }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_ArrayForIn_Valid_OK;
begin
  AnalyseSrc(SrcArrayForIn).Free();
end;

procedure TForInTests.TestSemantic_ArrayForIn_VarTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          Arr: array[0..4] of Integer;
          X:   string;
        begin
          for X in Arr do
            X := X
        end.
        ''');
end;

procedure TForInTests.TestSemantic_ArrayForIn_NonZeroBased_OK;
begin
  AnalyseSrc(SrcArrayForInNonZero).Free();
end;

{ ------------------------------------------------------------------ }
{ Shared sources — dynamic array                                       }
{ ------------------------------------------------------------------ }

const
  SrcDynArrayForIn =
    '''
        program P;
        var
          DA: array of Integer;
          X:  Integer;
        begin
          for X in DA do
            X := X + 1
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests — dynamic array                                       }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_DynArrayForIn_Valid_OK;
begin
  AnalyseSrc(SrcDynArrayForIn).Free();
end;

procedure TForInTests.TestSemantic_DynArrayForIn_VarTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          DA: array of Integer;
          X:  string;
        begin
          for X in DA do
            X := X
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Shared sources — string                                              }
{ ------------------------------------------------------------------ }

const
  SrcStringForIn =
    '''
        program P;
        var
          S: string;
          B: Byte;
        begin
          for B in S do
            B := 0
        end.
        ''';

  SrcStringForInIntVar =
    '''
        program P;
        var
          S: string;
          I: Integer;
        begin
          for I in S do
            I := 0
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests — string                                              }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_StringForIn_ByteVar_OK;
begin
  AnalyseSrc(SrcStringForIn).Free();
end;

procedure TForInTests.TestSemantic_StringForIn_IntVar_IsCodePointIter;
begin
  AnalyseSrc(SrcStringForInIntVar).Free();
end;

procedure TForInTests.TestSemantic_StringForIn_NonOrdinalVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          S: string;
          P: string;
        begin
          for P in S do
            P := P
        end.
        ''');
end;

procedure TForInTests.TestSemantic_StringForIn_WordVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          S: string;
          W: Word;
        begin
          for W in S do
            W := 0
        end.
        ''');
end;

procedure TForInTests.TestSemantic_StringForIn_SmallIntVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var
          S: string;
          N: SmallInt;
        begin
          for N in S do
            N := 0
        end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Shared sources — set iteration                                       }
{ ------------------------------------------------------------------ }

const
  SrcSetForIn =
    '''
        program P;
        type
          TColor = (Red, Green, Blue);
          TColorSet = set of TColor;
        var
          S: TColorSet;
          C: TColor;
        begin
          S := [Red, Blue];
          for C in S do
            WriteLn(Ord(C))
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests — set                                                 }
{ ------------------------------------------------------------------ }

procedure TForInTests.TestSemantic_SetForIn_Valid_OK;
begin
  AnalyseSrc(SrcSetForIn).Free();
end;

procedure TForInTests.TestSemantic_SetForIn_VarTypeMismatch_RaisesError;
begin
  { Loop variable must be ordinal — string is not ordinal }
  AnalyseExpectError(
    '''
        program P;
        type
          TColor = (Red, Green, Blue);
          TColorSet = set of TColor;
        var
          S: TColorSet;
          X: string;
        begin
          for X in S do
            X := X
        end.
        ''');
end;

procedure TForInTests.TestSemantic_SetForIn_NonSetCollNotAllowed;
begin
  { A plain Integer variable is not a valid for-in collection }
  AnalyseExpectError(
    '''
        program P;
        var
          N: Integer;
          X: Integer;
        begin
          for X in N do
            X := X
        end.
        ''');
end;

initialization
  RegisterTest(TForInTests);

end.
