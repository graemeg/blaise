{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.exceptions;

{ Tests for try/finally, try/except, and raise statements. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TExceptionTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Try_Keyword;
    procedure TestLexer_Finally_Keyword;
    procedure TestLexer_Except_Keyword;
    procedure TestLexer_Raise_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — try/finally                                                 }
    { ------------------------------------------------------------------ }
    procedure TestParse_TryFinally_IsTTryFinallyStmt;
    procedure TestParse_TryFinally_TryBodyStmtCount;
    procedure TestParse_TryFinally_FinallyBodyStmtCount;
    procedure TestParse_TryFinally_MultipleStmtsInTryBody;
    procedure TestParse_TryFinally_MultipleStmtsInFinallyBody;

    { ------------------------------------------------------------------ }
    { Parser — try/except                                                  }
    { ------------------------------------------------------------------ }
    procedure TestParse_TryExcept_IsTTryExceptStmt;
    procedure TestParse_TryExcept_TryBodyStmtCount;
    procedure TestParse_TryExcept_ExceptBodyStmtCount;

    { ------------------------------------------------------------------ }
    { Parser — raise                                                       }
    { ------------------------------------------------------------------ }
    procedure TestParse_Raise_IsTRaiseStmt;
    procedure TestParse_Raise_HasExpr;
    procedure TestParse_Raise_Bare_HasNilExpr;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TryFinally_OK;
    procedure TestSemantic_TryExcept_OK;
    procedure TestSemantic_Raise_ClassExpr_OK;
    procedure TestSemantic_Raise_NonClass_RaisesError;
    procedure TestSemantic_Raise_Bare_OK;
    procedure TestSemantic_ExceptionSubclass_CreateAndMessage_OK;

    { ------------------------------------------------------------------ }
    { Codegen — try/finally                                                }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — try/except                                                 }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — raise                                                      }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Codegen — setjmp-based real dispatch                                 }
    { ------------------------------------------------------------------ }
    { Exit inside try/finally must emit the finally body on the exit path,
      not just pop the frame. }
    { Exit inside the SECOND try block of a function must still pop its
      frame: the emitter's FExcDepth bookkeeping is per-path, and the
      exception path must rebalance it (regression: a double decrement left
      later try blocks at depth 0, so their Exit paths skipped the pop and
      left a stale g_exc_top -> crash on a later raise/pop). }

    { ------------------------------------------------------------------ }
    { Codegen — ARC cleanup on exception paths                            }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Parser — typed except handlers (on E: TClass do)                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_TypedExcept_HasOneHandler;
    procedure TestParse_TypedExcept_HandlerTypeName;
    procedure TestParse_TypedExcept_HandlerVarName;
    procedure TestParse_TypedExcept_HandlerBodyStmtCount;
    procedure TestParse_TypedExcept_TwoHandlers;
    procedure TestParse_TypedExcept_WithElseBody;
    procedure TestParse_TypedExcept_NoVarBinding;

    { ------------------------------------------------------------------ }
    { Semantic — typed except handlers                                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TypedExcept_SingleHandler_OK;
    procedure TestSemantic_TypedExcept_TwoHandlers_OK;
    procedure TestSemantic_TypedExcept_NonClassType_RaisesError;
    procedure TestSemantic_TypedExcept_WithElse_OK;
    procedure TestSemantic_TypedExcept_HandlerVarUsableInBody;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TExceptionTests.ParseSrc(const ASrc: string): TProgram;
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

function TExceptionTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TExceptionTests.AnalyseExpectError(const ASrc: string);
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
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcTryFinally =
    '''
        program P;
        var X: Integer;
        begin
          X := 0;
          try
            X := 1
          finally
            X := 2
          end
        end.
        ''';

  SrcTryFinallyMulti =
    '''
        program P;
        var X: Integer;
        var Y: Integer;
        begin
          try
            X := 1;
            Y := 2
          finally
            X := 0;
            Y := 0
          end
        end.
        ''';

  SrcTryExcept =
    '''
        program P;
        var X: Integer;
        begin
          X := 0;
          try
            X := 1
          except
            X := 99
          end
        end.
        ''';

  SrcRaise =
    '''
        program P;
        type
          TError = class
            Code: Integer;
          end;
        var E: TError;
        begin
          E := TError.Create();
          raise E
        end.
        ''';

  SrcBareRaise =
    '''
        program P;
        var X: Integer;
        begin
          try
            X := 1
          except
            raise
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestLexer_Try_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('try');
  try
    T := L.Next();
    AssertEquals('try token', Ord(tkTry), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Finally_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('finally');
  try
    T := L.Next();
    AssertEquals('finally token', Ord(tkFinally), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Except_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('except');
  try
    T := L.Next();
    AssertEquals('except token', Ord(tkExcept), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Raise_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('raise');
  try
    T := L.Next();
    AssertEquals('raise token', Ord(tkRaise), Ord(T.Kind));
  finally L.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser — try/finally                                                 }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TryFinally_IsTTryFinallyStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    AssertTrue('stmt is TTryFinallyStmt',
      Prog.Block.Stmts[1] is TTryFinallyStmt);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_TryBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_FinallyBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('finally body has 1 stmt', 1, TS.FinallyBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInTryBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi try body has 2 stmts', 2, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInFinallyBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi finally body has 2 stmts', 2, TS.FinallyBody.Stmts.Count);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser — try/except                                                  }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TryExcept_IsTTryExceptStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    AssertTrue('stmt is TTryExceptStmt',
      Prog.Block.Stmts[1] is TTryExceptStmt);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryExcept_TryBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryExcept_ExceptBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('except body has 1 stmt', 1, TS.ExceptBody.Stmts.Count);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Parser — raise                                                       }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_Raise_IsTRaiseStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcRaise);
  try
    AssertTrue('stmt is TRaiseStmt', Prog.Block.Stmts[1] is TRaiseStmt);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_Raise_HasExpr;
var Prog: TProgram; RS: TRaiseStmt;
begin
  Prog := ParseSrc(SrcRaise);
  try
    RS := TRaiseStmt(Prog.Block.Stmts[1]);
    AssertNotNull('raise has non-nil expression', RS.Expr);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_Raise_Bare_HasNilExpr;
var Prog: TProgram; TS: TTryExceptStmt; RS: TRaiseStmt;
begin
  Prog := ParseSrc(SrcBareRaise);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertTrue('except body stmt is TRaiseStmt',
      TS.ExceptBody.Stmts[0] is TRaiseStmt);
    RS := TRaiseStmt(TS.ExceptBody.Stmts[0]);
    AssertNull('bare raise has nil expression', RS.Expr);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestSemantic_TryFinally_OK;
begin
  AnalyseSrc(SrcTryFinally).Free();
end;

procedure TExceptionTests.TestSemantic_TryExcept_OK;
begin
  AnalyseSrc(SrcTryExcept).Free();
end;

procedure TExceptionTests.TestSemantic_Raise_ClassExpr_OK;
begin
  AnalyseSrc(SrcRaise).Free();
end;

procedure TExceptionTests.TestSemantic_Raise_NonClass_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
        begin
          X := 1;
          raise X
        end.
        ''');
end;

procedure TExceptionTests.TestSemantic_Raise_Bare_OK;
begin
  AnalyseSrc(SrcBareRaise).Free();
end;

procedure TExceptionTests.TestSemantic_ExceptionSubclass_CreateAndMessage_OK;
begin
  { Verify that an Exception base class with a string property and a subclass
    that inherits it can be declared, instantiated, and raised without semantic
    errors.  This mirrors the API exposed by stdlib/src/main/pascal/sysutils.pas. }
  AnalyseSrc(
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            constructor Create(AMessage: string);
            property Message: string read FMessage;
          end;
          ECompileError = class(Exception)
          end;
        constructor Exception.Create(AMessage: string);
        begin
          FMessage := AMessage;
        end;
        var E: ECompileError;
        begin
          E := ECompileError.Create('compile error');
          raise E
        end.
        ''').Free();
end;

{ ------------------------------------------------------------------ }
{ Codegen — setjmp-based real dispatch                                 }
{ ------------------------------------------------------------------ }

{ ------------------------------------------------------------------ }
{ Codegen — ARC cleanup on exception paths                            }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------ }
{ Shared source — typed except handlers                              }
{ ------------------------------------------------------------------ }

const
  SrcExcBase =
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            constructor Create(AMessage: string);
            property Message: string read FMessage;
          end;
          EFoo = class(Exception) end;
          EBar = class(Exception) end;
        constructor Exception.Create(AMessage: string);
        begin
          FMessage := AMessage;
        end;
        ''';

  SrcTypedExceptSingle =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42
          end
        end.
        ''';

  SrcTypedExceptTwo =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42;
            on E: EBar do
              X := 99
          end
        end.
        ''';

  SrcTypedExceptWithElse =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42
            else
              X := 0
          end
        end.
        ''';

  SrcTypedExceptNoVar =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on EFoo do
              X := 42
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser — typed except handlers                                     }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TypedExcept_HasOneHandler;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertEquals('one handler', 1, TES.Handlers.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerTypeName;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler type EFoo', 'EFoo', H.TypeName);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerVarName;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler var E', 'E', H.VarName);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerBodyStmtCount;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler body 1 stmt', 1, H.Body.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_TwoHandlers;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptTwo);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertEquals('two handlers', 2, TES.Handlers.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_WithElseBody;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptWithElse);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertNotNull('else body present', TES.ElseBody);
    AssertEquals('else body 1 stmt', 1, TES.ElseBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_NoVarBinding;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptNoVar);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('no-var handler: empty VarName', '', H.VarName);
    AssertEquals('no-var handler: TypeName is EFoo', 'EFoo', H.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — typed except handlers                                   }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestSemantic_TypedExcept_SingleHandler_OK;
begin
  AnalyseSrc(SrcTypedExceptSingle).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_TwoHandlers_OK;
begin
  AnalyseSrc(SrcTypedExceptTwo).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_NonClassType_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: Integer do
              X := 0
          end
        end.
        ''');
end;

procedure TExceptionTests.TestSemantic_TypedExcept_WithElse_OK;
begin
  AnalyseSrc(SrcTypedExceptWithElse).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_HandlerVarUsableInBody;
begin
  { Handler variable E should be in scope and usable inside the handler body. }
  AnalyseSrc(
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 0
          end
        end.
        ''').Free();
end;

initialization
  RegisterTest(TExceptionTests);

end.
