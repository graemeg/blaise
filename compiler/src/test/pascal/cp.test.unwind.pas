{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
{
  Exception unwind tables (docs/exception-unwind-cleanup-design.adoc).

  TUnwindAsmTests: the block every object carries, on both ISAs, and the
  invariant that the tables change no instruction (the routine text with and
  without --no-unwind-tables is identical once the unwind-only lines are
  removed).  TUnwindE2ETests: the runtime walk, on the host ISA.
}
unit cp.test.unwind;

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness, cp.test.e2e.base,
  uUnwindFacts;

type
  TUnwindAsmTests = class(TTestCase)
  private
    procedure CheckShape(const AAsm, ALocalPrefix, AWord, AZero: string);
    procedure CheckIdentity(const ATarget: string);
  published
    { one block per object: the magic, a routine record per routine, its
      labels in the right places }
    procedure TestBlock_ShapeAndLabels_Arm64;
    procedure TestBlock_ShapeAndLabels_X86_64;
    { the tables add data and labels, never an instruction }
    procedure TestTextIdentity_Arm64;
    procedure TestTextIdentity_X86_64;
  end;

  TUnwindE2ETests = class(TE2ETestCase)
  public
    procedure SetUp; override;
  published
    { a raise walks every Blaise frame up to the handler's, through deep
      recursion too, and is still caught }
    procedure TestRun_WalkFindsEveryFrame;
  end;

implementation

const
  ShapeSrc =
    '''
    program Shape;
    procedure Work;
    var S: string;
    begin
      S := 'x';
      WriteLn(S);
    end;
    begin
      Work();
    end.
    ''';

  { a mix of frames, temporaries, try blocks and closures }
  IdentitySrc =
    '''
    program Ident;
    type
      TErr = class
        Msg: string;
      end;
      TFn = reference to function(X: Int): Int;
      TRec = record A: string; B: Int; end;
      TObj = class
        Name: string;
        function Twice(X: Int): Int;
      end;
    function TObj.Twice(X: Int): Int;
    begin
      Result := X * 2;
    end;
    function MkStr(N: Int): string;
    begin
      Result := 'n' + Chr(N + 48) + '!';
    end;
    function Adder(K: Int): TFn;
    begin
      Result := function(X: Int): Int begin Result := X + K end;
    end;
    procedure Work(const A: string; B: string; R: TRec);
    var
      O: TObj;
      L: array of string;
      F: TFn;
      S: string;
    begin
      O := TObj.Create();
      SetLength(L, 2);
      L[0] := MkStr(1) + MkStr(2);
      F := Adder(3);
      try
        S := A + B + R.A + MkStr(F(O.Twice(4)));
        if Length(S) > 100 then raise TErr.Create();
      except
        on E: TErr do S := E.Msg;
      end;
      WriteLn(S, L[0]);
    end;
    var R: TRec;
    begin
      R.A := 'r';
      Work('a', 'b', R);
    end.
    ''';

function Lines(const S: string): TStringList;
begin
  Result := TStringList.Create();
  Result.Text := S;
end;

function IndexOfPrefix(L: TStringList; const APrefix: string; AFrom: Int): Int;
var
  I: Int;
begin
  for I := AFrom to L.Count - 1 do
    if Pos(APrefix, L.Strings[I]) = 0 then Exit(I);
  Result := -1;
end;

function IndexOfSub(L: TStringList; const ASub: string; AFrom: Int): Int;
var
  I: Int;
begin
  for I := AFrom to L.Count - 1 do
    if Pos(ASub, L.Strings[I]) >= 0 then Exit(I);
  Result := -1;
end;

{ The assembly with every unwind-only line removed: the labels (and the
  .text switch that opens the object's end-of-text label), the block (from
  its section directive to the section switch that ends it) and the
  _UnwindInit call in _main. }
function StripUnwind(const AAsm: string): string;
var
  L, R: TStringList;
  I: Int;
  S: string;
  InBlock: Boolean;
begin
  L := Lines(AAsm);
  R := TStringList.Create();
  try
    InBlock := False;
    for I := 0 to L.Count - 1 do
    begin
      S := L.Strings[I];
      if InBlock then
      begin
        if Trim(S) = '.text' then InBlock := False;
        Continue;
      end;
      if (Pos('__blaise_unw', S) >= 0) or (Pos('blaise_unwind', S) >= 0) then
      begin
        if Pos('.section', S) >= 0 then InBlock := True;
        Continue;
      end;
      if (Pos('unw_', S) >= 0) or (Pos('_UnwindInit', S) >= 0) then Continue;
      if (Trim(S) = '.text') and (I + 1 < L.Count) and
         (Pos('unw_hi', L.Strings[I + 1]) >= 0) then Continue;
      R.Add(S);
    end;
    Result := R.Text;
  finally
    R.Free();
    L.Free();
  end;
end;

procedure TUnwindAsmTests.CheckShape(const AAsm, ALocalPrefix, AWord, AZero: string);
var
  L: TStringList;
  Sym, Start, Cov, Sect: Int;
begin
  L := Lines(AAsm);
  try
    Sect := IndexOfSub(L, '.section', 0);
    while (Sect >= 0) and (IndexOfSub(L, 'unw', Sect) <> Sect) do
      Sect := IndexOfSub(L, '.section', Sect + 1);
    AssertTrue('an unwind section directive', Sect >= 0);
    AssertTrue('the block starts with the magic',
      IndexOfSub(L, AWord + ' ' + IntToStr(UNW_MAGIC), Sect) > Sect);
    Sym := IndexOfSub(L, 'Work:', 0);
    AssertTrue('routine symbol', Sym >= 0);
    Start := IndexOfPrefix(L, ALocalPrefix + 'unw_s', Sym);
    AssertEquals('the routine start label follows the symbol', Sym + 1, Start);
    Cov := IndexOfPrefix(L, ALocalPrefix + 'unw_c', Start);
    AssertTrue('a coverage label', Cov > Start);
    AssertTrue('the local is zeroed before coverage starts',
      (IndexOfSub(L, AZero, Start) > Start) and
      (IndexOfSub(L, AZero, Start) < Cov));
    AssertTrue('coverage starts before the exit label',
      IndexOfSub(L, 'exit', Cov) > Cov);
    AssertTrue('the routine record covers to its exit label',
      IndexOfSub(L, 'exit', Sect) > Sect);
    AssertTrue('a routine end label after the symbol',
      IndexOfPrefix(L, ALocalPrefix + 'unw_e', Cov) > Cov);
  finally
    L.Free();
  end;
end;

procedure TUnwindAsmTests.TestBlock_ShapeAndLabels_Arm64;
begin
  CheckShape(GenAsm(ShapeSrc, TargetArm64), 'L', '.word', 'xzr');
end;

procedure TUnwindAsmTests.TestBlock_ShapeAndLabels_X86_64;
begin
  CheckShape(GenAsm(ShapeSrc, TargetX86_64), '.L', '.long', '$0,');
end;

procedure TUnwindAsmTests.CheckIdentity(const ATarget: string);
var
  WithTables, Without: string;
begin
  WithTables := GenAsm(IdentitySrc, ATarget);
  GNoUnwindTables := True;
  try
    Without := GenAsm(IdentitySrc, ATarget);
  finally
    GNoUnwindTables := False;
  end;
  AssertTrue('the tables are present', Pos('unw_', WithTables) >= 0);
  AssertTrue('--no-unwind-tables emits none', Pos('unw_', Without) < 0);
  AssertEquals('instructions unchanged', Without, StripUnwind(WithTables));
end;

procedure TUnwindAsmTests.TestTextIdentity_Arm64;
begin
  CheckIdentity(TargetArm64);
end;

procedure TUnwindAsmTests.TestTextIdentity_X86_64;
begin
  CheckIdentity(TargetX86_64);
end;

procedure TUnwindE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-unwind');
end;

procedure TUnwindE2ETests.TestRun_WalkFindsEveryFrame;
begin
  AssertRunsOnAll(
    '''
    program Walk;
    uses SysUtils;
    function _UnwindLastWalk: Int; external name '_UnwindLastWalk';
    procedure P3;
    begin
      raise Exception.Create('deep');
    end;
    { a managed local keeps x86-64 from inlining a one-call body }
    procedure P2;
    var S: string;
    begin
      S := 'p' + Chr(50);
      P3();
      WriteLn(S);
    end;
    procedure P1;
    var S: string;
    begin
      S := 'p' + Chr(49);
      P2();
      WriteLn(S);
    end;
    procedure Recurse(N: Int);
    begin
      if N = 0 then raise Exception.Create('bottom');
      Recurse(N - 1);
    end;
    procedure Local;
    begin
      try
        raise Exception.Create('here');
      except
        on E: Exception do
          WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
    end;
    begin
      try
        P1();
      except
        on E: Exception do WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
      try
        Recurse(1000);
      except
        on E: Exception do WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
      Local();
    end.
    ''',
    'deep 3' + #10 + 'bottom 1001' + #10 + 'here 1' + #10, 0);
end;

initialization
  RegisterTest(TUnwindAsmTests);
  RegisterTest(TUnwindE2ETests);
end.
