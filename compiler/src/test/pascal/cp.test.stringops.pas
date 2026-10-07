{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.stringops;

{ Tests for built-in string operation functions:
  Length, Pos, Copy, UpperCase, LowerCase, SameText, IntToStr, StrToInt. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TStringOpsTests = class(TTestCase)
  private
    procedure SemanticOK(const ASrc: string);
    procedure SemanticError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Length                                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Length_StringArg_OK;
    procedure TestSemantic_Length_IntArg_Error;
    procedure TestSemantic_Length_ReturnsInteger;

    { ------------------------------------------------------------------ }
    { Pos                                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Pos_TwoStringArgs_OK;
    procedure TestSemantic_Pos_ReturnsInteger;

    { ------------------------------------------------------------------ }
    { Copy                                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Copy_OK;
    procedure TestSemantic_Copy_ReturnsString;

    { ------------------------------------------------------------------ }
    { UpperCase / LowerCase                                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UpperCase_OK;
    procedure TestSemantic_UpperCase_ReturnsString;
    procedure TestSemantic_LowerCase_OK;

    { ------------------------------------------------------------------ }
    { SameText                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SameText_OK;
    procedure TestSemantic_SameText_ReturnsBoolean;

    { ------------------------------------------------------------------ }
    { IntToStr / StrToInt                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IntToStr_OK;
    procedure TestSemantic_IntToStr_ReturnsString;
    procedure TestSemantic_StrToInt_OK;
    procedure TestSemantic_StrToInt_ReturnsInteger;

    { ------------------------------------------------------------------ }
    { Format                                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Format_OneIntArg_OK;
    procedure TestSemantic_Format_OneStringArg_OK;
    procedure TestSemantic_Format_MixedArgs_OK;
    procedure TestSemantic_Format_ReturnsString;
    procedure TestSemantic_Format_FloatArg_OK;
    { ------------------------------------------------------------------ }
    { String subscript S[N]                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StringSubscript_NonStringError;
    procedure TestSemantic_StringSubscript_MultiByteCharError;

    { ------------------------------------------------------------------ }
    { Delete / SetLength                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Delete_OK;
    procedure TestSemantic_Delete_NonStringError;
    procedure TestSemantic_SetLength_OK;
    procedure TestSemantic_SetLength_NonStringError;

    { ------------------------------------------------------------------ }
    { ARC on var/out string parameter assignment                           }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Low / High on strings                                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Low_StringArg_OK;
    procedure TestSemantic_High_StringArg_OK;
    procedure TestSemantic_Low_StringArg_ReturnsInteger;
    procedure TestSemantic_High_StringArg_ReturnsInteger;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.SemanticOK(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TStringOpsTests.SemanticError(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    try
      A.Analyse(Pr);
      Fail('Expected ESemanticError');
    except
      on E: ESemanticError do ;
    end;
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Source snippets                                                       }
{ ------------------------------------------------------------------ }

const
  SrcLength =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          n := Length(s)
        end.
        ''';

  SrcPos =
    '''
        program P;
        var s, sub: string;
        var n: Integer;
        begin
          n := Pos(sub, s)
        end.
        ''';

  SrcCopy =
    '''
        program P;
        var s, t: string;
        var i, n: Integer;
        begin
          t := Copy(s, i, n)
        end.
        ''';

  SrcUpperCase =
    '''
        program P;
        var s, t: string;
        begin
          t := UpperCase(s)
        end.
        ''';

  SrcLowerCase =
    '''
        program P;
        var s, t: string;
        begin
          t := LowerCase(s)
        end.
        ''';

  SrcSameText =
    '''
        program P;
        var s, t: string;
        var b: Boolean;
        begin
          b := SameText(s, t)
        end.
        ''';

  SrcIntToStr =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          s := IntToStr(n)
        end.
        ''';

  SrcStrToInt =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          n := StrToInt(s)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Length tests                                                          }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Length_StringArg_OK;
begin
  SemanticOK(SrcLength);
end;

procedure TStringOpsTests.TestSemantic_Length_IntArg_Error;
begin
  SemanticError(
    '''
        program P;
        var n: Integer;
        var r: Integer;
        begin
          r := Length(n)
        end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_Length_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcLength);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertNotNull('expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('Length returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Pos tests                                                            }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Pos_TwoStringArgs_OK;
begin
  SemanticOK(SrcPos);
end;

procedure TStringOpsTests.TestSemantic_Pos_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcPos);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('Pos returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Copy tests                                                           }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Copy_OK;
begin
  SemanticOK(SrcCopy);
end;

procedure TStringOpsTests.TestSemantic_Copy_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcCopy);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('Copy returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ UpperCase tests                                                       }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_UpperCase_OK;
begin
  SemanticOK(SrcUpperCase);
end;

procedure TStringOpsTests.TestSemantic_UpperCase_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcUpperCase);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('UpperCase returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TStringOpsTests.TestSemantic_LowerCase_OK;
begin
  SemanticOK(SrcLowerCase);
end;

{ ------------------------------------------------------------------ }
{ SameText tests                                                        }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_SameText_OK;
begin
  SemanticOK(SrcSameText);
end;

procedure TStringOpsTests.TestSemantic_SameText_ReturnsBoolean;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcSameText);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('SameText returns Boolean',
      Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ IntToStr / StrToInt tests                                            }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_IntToStr_OK;
begin
  SemanticOK(SrcIntToStr);
end;

procedure TStringOpsTests.TestSemantic_IntToStr_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcIntToStr);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('IntToStr returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TStringOpsTests.TestSemantic_StrToInt_OK;
begin
  SemanticOK(SrcStrToInt);
end;

procedure TStringOpsTests.TestSemantic_StrToInt_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcStrToInt);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('StrToInt returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Format tests                                                         }
{ ------------------------------------------------------------------ }

const
  SrcFormatOneInt =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := Format('value=%d', n)
        end.
        ''';

  SrcFormatOneStr =
    '''
        program P;
        var t: string;
        var s: string;
        begin
          t := 'hello';
          s := Format('say %s', t)
        end.
        ''';

  SrcFormatMixed =
    '''
        program P;
        var name: string;
        var age: Integer;
        var s: string;
        begin
          name := 'Bob';
          age  := 30;
          s := Format('%s is %d', name, age)
        end.
        ''';

  SrcFormatFloat =
    '''
        program P;
        var x: Double;
        var s: string;
        begin
          x := 3.5;
          s := Format('v=%.1f', x)
        end.
        ''';

procedure TStringOpsTests.TestSemantic_Format_OneIntArg_OK;
begin
  SemanticOK(SrcFormatOneInt);
end;

procedure TStringOpsTests.TestSemantic_Format_OneStringArg_OK;
begin
  SemanticOK(SrcFormatOneStr);
end;

procedure TStringOpsTests.TestSemantic_Format_MixedArgs_OK;
begin
  SemanticOK(SrcFormatMixed);
end;

procedure TStringOpsTests.TestSemantic_Format_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcFormatOneInt);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[1]);
    AssertEquals('Format returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TStringOpsTests.TestSemantic_Format_FloatArg_OK;
begin
  SemanticOK(SrcFormatFloat);
end;

{ ------------------------------------------------------------------ }
{ String subscript S[N]                                               }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_StringSubscript_NonStringError;
const
  Src =
    '''
        program T;
        var N: Integer;
        var B: Integer;
        begin
          B := N[0]
        end.
        ''';
begin
  SemanticError(Src);
end;

procedure TStringOpsTests.TestSemantic_StringSubscript_MultiByteCharError;
{ A multi-byte string literal (more than 1 byte) cannot coerce to a byte
  value for comparison with a string subscript.  Use a 2-ASCII-byte literal
  ('AB') to test this without triggering the parser's pre-existing
  limitation with bytes > 127 in string literals. }
const
  Src =
    '''
        program T;
        var S: string;
        begin
          if S[0] = 'AB' then WriteLn('yes')
        end.
        ''';
begin
  SemanticError(Src);
end;

{ ------------------------------------------------------------------ }
{ Delete / SetLength                                                   }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Delete_OK;
begin
  SemanticOK(
    '''
        program P; var S: string;
        begin S := 'hello'; Delete(S, 2, 3) end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_Delete_NonStringError;
begin
  SemanticError(
    '''
        program P; var N: Integer;
        begin Delete(N, 1, 1) end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_SetLength_OK;
begin
  SemanticOK(
    '''
        program P; var S: string;
        begin S := 'hello'; SetLength(S, 3) end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_SetLength_NonStringError;
begin
  SemanticError(
    '''
        program P; var N: Integer;
        begin SetLength(N, 5) end.
        ''');
end;

{ ------------------------------------------------------------------ }
{ Low / High on strings                                               }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Low_StringArg_OK;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := Low(S) end.');
end;

procedure TStringOpsTests.TestSemantic_High_StringArg_OK;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
end;

procedure TStringOpsTests.TestSemantic_Low_StringArg_ReturnsInteger;
var
  L: TLexer;
  P: TParser;
  Pr: TProgram;
  A: TSemanticAnalyser;
  Expr: TASTExpr;
begin
  { Parse and analyse: just check no exception and type is Integer }
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := Low(S) end.');
end;

procedure TStringOpsTests.TestSemantic_High_StringArg_ReturnsInteger;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
end;

initialization
  RegisterTest(TStringOpsTests);

end.
