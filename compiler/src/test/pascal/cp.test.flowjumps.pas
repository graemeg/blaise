{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.flowjumps;

{ Tests for non-local flow statements: Exit and Break. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TFlowJumpsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestLexer_Exit_Keyword;
    procedure TestLexer_Break_Keyword;
    procedure TestParse_Exit_IsExitStmt;
    procedure TestParse_Break_IsBreakStmt;
    procedure TestSemantic_Break_OutsideLoop_RaisesError;
    procedure TestSemantic_Break_InsideFor_Resolves;
    procedure TestSemantic_Break_InsideWhile_Resolves;

    { Exit(Value) function-result shorthand }
    procedure TestParse_ExitValue_AttachesValue;
    procedure TestSemantic_ExitValue_InFunction_OK;
    procedure TestSemantic_ExitValue_InProcedure_RaisesError;
    procedure TestSemantic_ExitValue_TypeMismatch_RaisesError;
  end;

implementation

function TFlowJumpsTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TFlowJumpsTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

procedure TFlowJumpsTests.AnalyseExpectError(const ASrc: string);
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

const
  SrcExit =
    '''
        program P;
        var I: Integer;
        begin
          I := 1;
          if I = 1 then exit;
          I := 2
        end.
        ''';

  SrcBreakInFor =
    '''
        program P;
        var I: Integer;
        begin
          for I := 1 to 10 do
          begin
            if I > 5 then break
          end
        end.
        ''';

  SrcBreakInWhile =
    '''
        program P;
        var I: Integer;
        begin
          I := 0;
          while I < 100 do
          begin
            if I = 5 then break;
            I := I + 1
          end
        end.
        ''';

  SrcBreakOutsideLoop =
    '''
        program P;
        var I: Integer;
        begin
          I := 0;
          break
        end.
        ''';

  SrcExitFromFunc =
    '''
        program P;
        function Abs1(X: Integer): Integer;
        begin
          if X < 0 then
          begin Result := 0 - X; exit end;
          Result := X
        end;
        var N: Integer;
        begin
          N := Abs1(-7)
        end.
        ''';

  { Exit(X) inside a function — assigns X to Result, then returns. }
  SrcExitValueFunc =
    '''
        program P;
        function Classify(N: Integer): Integer;
        begin
          if N < 0 then Exit(-1);
          Result := 1
        end;
        var R: Integer;
        begin
          R := Classify(-3)
        end.
        ''';

  { Exit(X) in a procedure — illegal (no Result). }
  SrcExitValueProc =
    '''
        program P;
        procedure DoIt;
        begin
          Exit(5)
        end;
        begin
          DoIt()
        end.
        ''';

  { Exit(X) where X is not assignment-compatible with the return type. }
  SrcExitValueMismatch =
    '''
        program P;
        function F: Integer;
        begin
          Exit('text')
        end;
        var R: Integer;
        begin
          R := F
        end.
        ''';

procedure TFlowJumpsTests.TestLexer_Exit_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('exit');
  try T := L.Next(); AssertEquals(Ord(tkExit), Ord(T.Kind)); finally L.Free(); end;
end;

procedure TFlowJumpsTests.TestLexer_Break_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('break');
  try T := L.Next(); AssertEquals(Ord(tkBreak), Ord(T.Kind)); finally L.Free(); end;
end;

procedure TFlowJumpsTests.TestParse_Exit_IsExitStmt;
var Prog: TProgram; IfS: TIfStmt;
begin
  Prog := ParseSrc(SrcExit);
  try
    IfS := TIfStmt(Prog.Block.Stmts[1]);
    AssertTrue('then body is TExitStmt', IfS.ThenStmt is TExitStmt);
  finally Prog.Free(); end;
end;

procedure TFlowJumpsTests.TestParse_Break_IsBreakStmt;
var
  Prog: TProgram;
  ForS: TForStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
begin
  Prog := ParseSrc(SrcBreakInFor);
  try
    ForS := TForStmt(Prog.Block.Stmts[0]);
    Cmp  := TCompoundStmt(ForS.Body);
    IfS  := TIfStmt(Cmp.Stmts[0]);
    AssertTrue('then body is TBreakStmt', IfS.ThenStmt is TBreakStmt);
  finally Prog.Free(); end;
end;

procedure TFlowJumpsTests.TestSemantic_Break_OutsideLoop_RaisesError;
begin
  AnalyseExpectError(SrcBreakOutsideLoop);
end;

procedure TFlowJumpsTests.TestSemantic_Break_InsideFor_Resolves;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcBreakInFor);
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

procedure TFlowJumpsTests.TestSemantic_Break_InsideWhile_Resolves;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcBreakInWhile);
  try AssertNotNull(Prog); finally Prog.Free(); end;
end;

{ -------------------------------------------------------------------- }
{ Exit(Value) function-result shorthand                                  }
{ -------------------------------------------------------------------- }

procedure TFlowJumpsTests.TestParse_ExitValue_AttachesValue;
var Prog: TProgram; MDecl: TMethodDecl; IfS: TIfStmt; ExitS: TExitStmt;
begin
  { function Classify: first body statement is the 'if N < 0 then Exit(-1)'. }
  Prog := ParseSrc(SrcExitValueFunc);
  try
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    IfS   := TIfStmt(MDecl.Body.Stmts[0]);
    AssertTrue('then body is TExitStmt', IfS.ThenStmt is TExitStmt);
    ExitS := TExitStmt(IfS.ThenStmt);
    AssertNotNull('Exit value attached', ExitS.Value);
  finally Prog.Free(); end;
end;

procedure TFlowJumpsTests.TestSemantic_ExitValue_InFunction_OK;
var Prog: TProgram;
begin
  { Analyses cleanly and rewrites into a synthesised Result assignment. }
  Prog := AnalyseSrc(SrcExitValueFunc);
  try
    { After analysis, the parsed Value moved into ResultAssign. }
    { (Navigation kept light — TestParse covers the shape; here we just
      confirm analysis does not raise.) }
  finally Prog.Free(); end;
end;

procedure TFlowJumpsTests.TestSemantic_ExitValue_InProcedure_RaisesError;
begin
  AnalyseExpectError(SrcExitValueProc);
end;

procedure TFlowJumpsTests.TestSemantic_ExitValue_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(SrcExitValueMismatch);
end;

initialization
  RegisterTest(TFlowJumpsTests);

end.
