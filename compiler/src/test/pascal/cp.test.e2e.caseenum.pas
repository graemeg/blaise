{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.caseenum;

{ E2E tests for case statements and enum types. }

interface

uses
  blaise.testing, classes, cp.test.e2e.base;

type
  [Threaded]
  TE2ECaseEnumTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Case_IntegerBranch;
    procedure TestRun_Case_ElseBranch;
    procedure TestRun_Enum_OrdinalValues;
    procedure TestRun_Enum_InCase;
    procedure TestRun_Enum_ExplicitOrdinals;
    procedure TestRun_Enum_AutoContinueAfterExplicit;
    procedure TestRun_Enum_ExplicitInCase;
    procedure TestRun_Enum_ScopedAccess;
    procedure TestRun_Enum_SharedMemberByContext;
    procedure TestRun_Enum_AmbiguousBareRejected;
    procedure TestRun_Enum_CallArgByContext;
    procedure TestRun_Enum_ForBoundsByContext;
    procedure TestRun_Enum_FieldAssignByContext;
    procedure TestRun_Enum_MethodArgByContext;
    procedure TestRun_Enum_ArrayElemByContext;
    procedure TestRun_Enum_PointerWriteByContext;
    procedure TestRun_Enum_ProcTypeArgByContext;
    procedure TestRun_Enum_ReturnByContext;
    { High/Low of an enum type fold to compile-time ordinals — the MAX / MIN
      stored ordinal, which for a contiguous 0-based enum is member-count-1 / 0
      but for an explicit-ordinal enum is the real max/min
      (BUG-20260720-enum-explicit-ordinal-highlow). }
    procedure TestRun_Enum_HighLowBounds;
    procedure TestRun_Enum_HighLow_ExplicitOrdinals;
    procedure TestRun_Enum_HighLow_PartialExplicit;
    procedure TestRun_Enum_HighLow_NonMonotonic;
    procedure TestRun_Enum_HighLow_NegativeOrdinal;
    procedure TestRun_Enum_HighLow_SingleExplicit;
    procedure TestRun_Enum_HighLow_ForRange;
    procedure TestRun_Enum_ExplicitOrdinal_RecordField;
  end;

implementation

procedure TE2ECaseEnumTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-caseenum');
end;

const
  SrcCaseInt =
    '''
        program P;
        var N: Integer;
        begin
          N := 2;
          case N of
            1: WriteLn(11);
            2: WriteLn(22);
            3: WriteLn(33)
          end
        end.
        ''';

  SrcCaseElse =
    '''
        program P;
        var N: Integer;
        begin
          N := 7;
          case N of
            1: WriteLn(1);
            2: WriteLn(2)
          else
            WriteLn(99)
          end
        end.
        ''';

  SrcEnumOrdinal =
    '''
        program P;
        type
          TColor = (cRed, cGreen, cBlue);
        var C: TColor;
        begin
          C := cRed;   WriteLn(C);
          C := cGreen; WriteLn(C);
          C := cBlue;  WriteLn(C)
        end.
        ''';

  SrcEnumCase =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        var D: TDir;
        begin
          D := dEast;
          case D of
            dNorth: WriteLn(0);
            dSouth: WriteLn(1);
            dEast:  WriteLn(2);
            dWest:  WriteLn(3)
          end
        end.
        ''';

procedure TE2ECaseEnumTests.TestRun_Case_IntegerBranch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseInt, '22' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Case_ElseBranch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseElse, '99' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_OrdinalValues;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcEnumOrdinal, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('cRed=0',   '0', Lines.Strings[0]);
    AssertEquals('cGreen=1', '1', Lines.Strings[1]);
    AssertEquals('cBlue=2',  '2', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_InCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcEnumCase, '2' + LineEnding, 0);
end;

const
  SrcExplicitOrdinals =
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        var S: TStatus;
        begin
          S := Idle;    WriteLn(S);
          S := Running; WriteLn(S);
          S := Done;    WriteLn(S)
        end.
        ''';

  SrcAutoContinue =
    '''
        program P;
        type
          TCode = (A=100, B, C);
        var X: TCode;
        begin
          X := A; WriteLn(X);
          X := B; WriteLn(X);
          X := C; WriteLn(X)
        end.
        ''';

  SrcExplicitInCase =
    '''
        program P;
        type
          THTTPStatus = (OK=200, NotFound=404, ServerError=500);
        var S: THTTPStatus;
        begin
          S := NotFound;
          case S of
            200: WriteLn('ok');
            404: WriteLn('not found');
            500: WriteLn('server error')
          else
            WriteLn('unknown')
          end
        end.
        ''';

procedure TE2ECaseEnumTests.TestRun_Enum_ExplicitOrdinals;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExplicitOrdinals, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Idle=10',    '10', Lines.Strings[0]);
    AssertEquals('Running=20', '20', Lines.Strings[1]);
    AssertEquals('Done=30',    '30', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_AutoContinueAfterExplicit;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcAutoContinue, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A=100', '100', Lines.Strings[0]);
    AssertEquals('B=101', '101', Lines.Strings[1]);
    AssertEquals('C=102', '102', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ExplicitInCase;
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExplicitInCase, Output, RCode));
  AssertEquals('NotFound=404 matches case 404', 'not found', Trim(Output));
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ScopedAccess;
const
  { Two enums in one unit share the member name 'Red'.  Members are not bare
    global symbols, so each enum's members are reachable through the
    type-qualified form regardless of the shared name. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        begin
          WriteLn(Ord(TColorA.Red));
          WriteLn(Ord(TColorA.Green));
          WriteLn(Ord(TColorB.Red));
          WriteLn(Ord(TColorB.Blue))
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('TColorA.Red',  '0', Lines.Strings[0]);
    AssertEquals('TColorA.Green','1', Lines.Strings[1]);
    AssertEquals('TColorB.Red',  '0', Lines.Strings[2]);
    AssertEquals('TColorB.Blue', '1', Lines.Strings[3]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_SharedMemberByContext;
const
  { 'Red' is shared by both enums.  Each bare use is disambiguated by its
    context — assignment target, case selector, set element — so the program
    reaches the correct member of each enum at runtime. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Red, Blue);
        var
          a: TColorA;
          b: TColorB;
          s: set of TColorA;
        begin
          a := Red;            WriteLn(Ord(a));
          b := Blue;           WriteLn(Ord(b));
          s := [Red, Green];
          if Red in s then WriteLn(10);
          case b of
            Red:  WriteLn(20);
            Blue: WriteLn(21)
          end
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('a := Red (TColorA.Red)',  '0',  Lines.Strings[0]);
    AssertEquals('b := Blue (TColorB.Blue)','1',  Lines.Strings[1]);
    AssertEquals('Red in s (TColorA.Red)',  '10', Lines.Strings[2]);
    AssertEquals('case b = Blue',           '21', Lines.Strings[3]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_AmbiguousBareRejected;
const
  { A bare, context-free reference to a member shared by two enums cannot be
    resolved and must fail to compile — there is no last-wins fallback. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red);
        begin
          WriteLn(Ord(Red))
        end.
        ''';
var Output: string; RCode: Integer; Rejected: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Rejected := False;
  try
    if not CompileAndRun(Src, Output, RCode) then
      Rejected := True;
  except
    on E: Exception do Rejected := True;
  end;
  AssertTrue('ambiguous bare member must not compile', Rejected);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_CallArgByContext;
const
  { 'Red' is shared (ordinal 0 in TColorA, ordinal 1 in TColorB).  Each bare
    member passed as a call argument is steered to the enum of the callee's
    parameter, so the right ordinal reaches the routine at runtime. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
        procedure TakeA(c: TColorA);
        begin WriteLn(Ord(c)) end;
        procedure TakeB(c: TColorB);
        begin WriteLn(Ord(c)) end;
        begin
          TakeA(Red);
          TakeB(Red);
          TakeB(Blue)
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('TakeA(Red) -> TColorA.Red',  '0', Lines.Strings[0]);
    AssertEquals('TakeB(Red) -> TColorB.Red',  '1', Lines.Strings[1]);
    AssertEquals('TakeB(Blue) -> TColorB.Blue','2', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ForBoundsByContext;
const
  { The loop variable's type disambiguates the bare shared start bound 'Red'
    (TColorB here), so the loop walks TColorB.Red(1)..TColorB.Blue(2). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
        var b: TColorB;
        begin
          for b := Red to Blue do
            WriteLn(Ord(b))
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('first iter b=Red(1)',  '1', Lines.Strings[0]);
    AssertEquals('second iter b=Blue(2)','2', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_FieldAssignByContext;
const
  { A bare shared member assigned to a record field is disambiguated by the
    field's enum type (TColorB), so r.c receives TColorB.Red (ordinal 1). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
          TRec = record c: TColorB; end;
        var r: TRec;
        begin
          r.c := Red;
          WriteLn(Ord(r.c))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('r.c := Red -> TColorB.Red (ordinal 1)', '1', Trim(Output));
end;

procedure TE2ECaseEnumTests.TestRun_Enum_MethodArgByContext;
const
  { A bare shared member passed to a method is steered to the enum of the
    method's parameter (TColorB), so TColorB.Red (ordinal 1) reaches it. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
          TFoo = class
            procedure TakeB(c: TColorB);
          end;
        procedure TFoo.TakeB(c: TColorB);
        begin WriteLn(Ord(c)) end;
        var f: TFoo;
        begin
          f := TFoo.Create();
          f.TakeB(Red);
          f.TakeB(Blue);
          f.Free()
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('TakeB(Red) -> TColorB.Red',  '1', Lines.Strings[0]);
    AssertEquals('TakeB(Blue) -> TColorB.Blue','2', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ArrayElemByContext;
const
  { Writing a bare shared member into an array element is disambiguated by the
    array's element type (TColorB), so arr[0] receives TColorB.Red (ordinal 1). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
        var arr: array[0..1] of TColorB;
        begin
          arr[0] := Red;
          arr[1] := Blue;
          WriteLn(Ord(arr[0]));
          WriteLn(Ord(arr[1]))
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('arr[0] := Red -> TColorB.Red',  '1', Lines.Strings[0]);
    AssertEquals('arr[1] := Blue -> TColorB.Blue','2', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_PointerWriteByContext;
const
  { Writing a bare shared member through a typed pointer is disambiguated by
    the pointer's base enum type (TColorB), so the target receives ordinal 2. }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
          PColorB = ^TColorB;
        var
          b: TColorB;
          q: PColorB;
        begin
          q := @b;
          q^ := Blue;
          WriteLn(Ord(b))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('q^ := Blue -> TColorB.Blue (ordinal 2)', '2', Trim(Output));
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ProcTypeArgByContext;
const
  { Calling through a procedural-type variable steers a bare shared member to
    the enum of the procedural type's parameter (TColorB). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
          TProcB = procedure(c: TColorB);
        procedure ShowB(c: TColorB);
        begin WriteLn(Ord(c)) end;
        var cb: TProcB;
        begin
          cb := @ShowB;
          cb(Red);
          cb(Blue)
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('cb(Red) -> TColorB.Red',  '1', Lines.Strings[0]);
    AssertEquals('cb(Blue) -> TColorB.Blue','2', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ReturnByContext;
const
  { A bare shared member returned from a function is disambiguated by the
    function's return enum, via both Result := and Exit(). }
  Src =
    '''
        program P;
        type
          TColorA = (Red, Green);
          TColorB = (Amber, Red, Blue);
        function ViaResult: TColorB;
        begin Result := Red end;
        function ViaExit: TColorB;
        begin Exit(Blue) end;
        begin
          WriteLn(Ord(ViaResult()));
          WriteLn(Ord(ViaExit()))
        end.
        ''';
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Result := Red -> TColorB.Red',  '1', Lines.Strings[0]);
    AssertEquals('Exit(Blue) -> TColorB.Blue',    '2', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLowBounds;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Contiguous enum: High(TColor) = last member (Blue = 2); Low(TColor) = 0.
    This is the no-regression case for the explicit-ordinal fix. }
  AssertRunsOnAll('''
    program Prg;
    type TColor = (Red, Green, Blue);
    var A: array[0..7] of Integer;
    begin
      WriteLn(Ord(High(TColor)));
      WriteLn(Ord(Low(TColor)));
      WriteLn(Length(A))
    end.
    ''', '2' + LineEnding + '0' + LineEnding + '8' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_ExplicitOrdinals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Explicit ordinals: High = max (10), Low = min (5) — NOT count-1 / 0. }
  AssertRunsOnAll('''
    program Prg;
    type TE = (A = 5, B = 10);
    begin
      WriteLn(Ord(A));
      WriteLn(Ord(B));
      WriteLn(Ord(High(TE)));
      WriteLn(Ord(Low(TE)))
    end.
    ''', '5' + LineEnding + '10' + LineEnding + '10' + LineEnding + '5' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_PartialExplicit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Partial explicit: C auto-continues from B=5 to 6; High = 6, Low = 0. }
  AssertRunsOnAll('''
    program Prg;
    type TE = (A, B = 5, C);
    begin
      WriteLn(Ord(C));
      WriteLn(Ord(High(TE)));
      WriteLn(Ord(Low(TE)))
    end.
    ''', '6' + LineEnding + '6' + LineEnding + '0' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_NonMonotonic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Non-monotonic (legal in Blaise): the last member is NOT the max, so High
    must fold the MAX over all members (20), not the last (15). }
  AssertRunsOnAll('''
    program Prg;
    type TE = (A = 10, B = 20, C = 15);
    begin
      WriteLn(Ord(High(TE)));
      WriteLn(Ord(Low(TE)))
    end.
    ''', '20' + LineEnding + '10' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_NegativeOrdinal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Negative min ordinal: Low must fold to -3 (signed), not 0. }
  AssertRunsOnAll('''
    program Prg;
    type TE = (A = -3, B = 2);
    begin
      WriteLn(Ord(High(TE)));
      WriteLn(Ord(Low(TE)))
    end.
    ''', '2' + LineEnding + '-3' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_SingleExplicit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Single explicit member: High = Low = 42. }
  AssertRunsOnAll('''
    program Prg;
    type TE = (Only = 42);
    begin
      WriteLn(Ord(High(TE)));
      WriteLn(Ord(Low(TE)))
    end.
    ''', '42' + LineEnding + '42' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_HighLow_ForRange;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { for e := Low(TE) to High(TE) must iterate the real ordinal range 5..10
    (6 values), not 0..1. }
  AssertRunsOnAll('''
    program Prg;
    type TE = (A = 5, B = 10);
    var e: TE; n: Integer;
    begin
      n := 0;
      for e := Low(TE) to High(TE) do n := n + 1;
      WriteLn(n)
    end.
    ''', '6' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ExplicitOrdinal_RecordField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Ord() of an explicit-ordinal enum stored in a record field must read the
    real ordinal (companion fix to TEnumTypeDesc.OrdinalOf). }
  AssertRunsOnAll('''
    program Prg;
    type
      TE = (A = 5, B = 10);
      TR = record E: TE; end;
    var r: TR;
    begin
      r.E := B;
      WriteLn(Ord(r.E))
    end.
    ''', '10' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2ECaseEnumTests);

end.
