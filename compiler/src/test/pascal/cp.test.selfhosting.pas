{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.selfhosting;

{ Tests for the two remaining self-hosting gaps:
    1. Multiple type/var sections in a single block
    2. File I/O and CLI builtins: ParamStr, ParamCount, ReadFile, WriteFile,
       FileExists, GetEnvVar, Exec, Halt }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TSelfHostingTests = class(TTestCase)
  private
    procedure SemanticOK(const ASrc: string);
    procedure ParseOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Multi-section type/var block (Gap 1)                                }
    { ------------------------------------------------------------------ }
    procedure TestParse_MultiTypeSection_TwoTypeBlocks;
    procedure TestParse_MultiTypeSection_TypeVarTypeVar;
    procedure TestParse_MultiTypeSection_VarThenType;
    procedure TestSemantic_MultiTypeSection_TwoClasses_OK;

    { ------------------------------------------------------------------ }
    { ParamCount / ParamStr (Gap 2 — CLI args)                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ParamCount_ReturnsInteger;
    procedure TestSemantic_ParamStr_ReturnsString;

    { ------------------------------------------------------------------ }
    { ReadFile / WriteFile / FileExists (Gap 2 — file I/O)               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ReadFile_ReturnsString;
    procedure TestSemantic_WriteFile_OK;
    procedure TestSemantic_FileExists_ReturnsBoolean;
    procedure TestSemantic_FileAge_ReturnsInt64;

    { ------------------------------------------------------------------ }
    { GetEnvVar / Exec / Halt (Gap 2 — environment and process)          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GetEnvVar_ReturnsString;
    procedure TestSemantic_Exec_ReturnsInteger;
    procedure TestSemantic_Halt_OK;
    procedure TestSemantic_GetEnvironmentVariable_ReturnsString;

    { ------------------------------------------------------------------ }
    { File path manipulation (step 11)                                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ChangeFileExt_ReturnsString;
    procedure TestSemantic_ExtractFileName_ReturnsString;
    procedure TestSemantic_ExtractFilePath_ReturnsString;
    procedure TestSemantic_IncludeTrailingPathDelimiter_ReturnsString;

    { ------------------------------------------------------------------ }
    { MaxInt built-in constant                                            }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_MaxInt_ResolvesToInt64;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Gap 1: multiple type sections }
  SrcTwoTypeBlocks =
    '''
        program P;
        type
          TA = class
            FX: Integer;
          end;
        type
          TB = class
            FY: Integer;
          end;
        begin
        end.
        ''';

  SrcTypeVarTypeVar =
    '''
        program P;
        type
          TA = class
            FX: Integer;
          end;
        var
          A: TA;
        type
          TB = class
            FY: Integer;
          end;
        var
          B: TB;
        begin
        end.
        ''';

  SrcVarThenType =
    '''
        program P;
        var
          N: Integer;
        type
          TA = class
            FX: Integer;
          end;
        begin
        end.
        ''';

  SrcTwoClassesBothUsed =
    '''
        program P;
        type
          TA = class
            FX: Integer;
          end;
        type
          TB = class
            FY: Integer;
          end;
        var
          A: TA;
          B: TB;
        begin
          A := TA.Create();
          B := TB.Create()
        end.
        ''';

  { Gap 2: CLI args }
  SrcParamCount =
    '''
        program P;
        var N: Integer;
        begin
          N := ParamCount()
        end.
        ''';

  SrcParamStr =
    '''
        program P;
        var S: string;
        begin
          S := ParamStr(0)
        end.
        ''';

  { Gap 2: file I/O }
  SrcReadFile =
    '''
        program P;
        var S: string;
        begin
          S := ReadFile('test.txt')
        end.
        ''';

  SrcWriteFile =
    '''
        program P;
        begin
          WriteFile('out.txt', 'hello')
        end.
        ''';

  SrcFileExists =
    '''
        program P;
        var B: Boolean;
        begin
          B := FileExists('test.txt')
        end.
        ''';

  SrcFileAge =
    '''
        program P;
        var A: Int64;
        begin
          A := FileAge('test.txt')
        end.
        ''';

  { Gap 2: environment and process }
  SrcGetEnvVar =
    '''
        program P;
        var S: string;
        begin
          S := GetEnvVar('PATH')
        end.
        ''';

  SrcGetEnvironmentVariable =
    '''
        program P;
        var S: string;
        begin
          S := GetEnvironmentVariable('PATH')
        end.
        ''';

  SrcExec =
    '''
        program P;
        var N: Integer;
        begin
          N := Exec('echo hello')
        end.
        ''';

  SrcHalt =
    '''
        program P;
        begin
          Halt(0)
        end.
        ''';

  { Step 11: file path manipulation }
  SrcChangeFileExt =
    '''
        program P;
        var S: string;
        begin
          S := ChangeFileExt('test.pas', '.bak')
        end.
        ''';

  SrcExtractFileName =
    '''
        program P;
        var S: string;
        begin
          S := ExtractFileName('/usr/bin/ls')
        end.
        ''';

  SrcExtractFilePath =
    '''
        program P;
        var S: string;
        begin
          S := ExtractFilePath('/usr/bin/ls')
        end.
        ''';

  SrcIncludeTrailingPathDelimiter =
    '''
        program P;
        var S: string;
        begin
          S := IncludeTrailingPathDelimiter('/usr/bin')
        end.
        ''';

  SrcMaxInt =
    '''
        program P;
        var N: Int64;
        begin
          N := MaxInt;
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.SemanticOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

procedure TSelfHostingTests.ParseOK(const ASrc: string);
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
    Par.Free();
    Lex.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Gap 1: multiple type/var sections                                    }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestParse_MultiTypeSection_TwoTypeBlocks;
begin
  ParseOK(SrcTwoTypeBlocks);
end;

procedure TSelfHostingTests.TestParse_MultiTypeSection_TypeVarTypeVar;
begin
  ParseOK(SrcTypeVarTypeVar);
end;

procedure TSelfHostingTests.TestParse_MultiTypeSection_VarThenType;
begin
  ParseOK(SrcVarThenType);
end;

procedure TSelfHostingTests.TestSemantic_MultiTypeSection_TwoClasses_OK;
begin
  SemanticOK(SrcTwoClassesBothUsed);
end;

{ ------------------------------------------------------------------ }
{ Gap 2: CLI args                                                      }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_ParamCount_ReturnsInteger;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Ass:  TAssignment;
begin
  Lex  := TLexer.Create(SrcParamCount);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Ass := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('ParamCount returns Integer',
    Ord(tyInteger), Ord(Ass.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TSelfHostingTests.TestSemantic_ParamStr_ReturnsString;
begin
  SemanticOK(SrcParamStr);
end;

{ ------------------------------------------------------------------ }
{ Gap 2: file I/O                                                      }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_ReadFile_ReturnsString;
begin
  SemanticOK(SrcReadFile);
end;

procedure TSelfHostingTests.TestSemantic_WriteFile_OK;
begin
  SemanticOK(SrcWriteFile);
end;

procedure TSelfHostingTests.TestSemantic_FileExists_ReturnsBoolean;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Ass:  TAssignment;
begin
  Lex  := TLexer.Create(SrcFileExists);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Ass := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('FileExists returns Boolean',
    Ord(tyBoolean), Ord(Ass.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TSelfHostingTests.TestSemantic_FileAge_ReturnsInt64;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Ass:  TAssignment;
begin
  Lex  := TLexer.Create(SrcFileAge);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Ass := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('FileAge returns Int64',
    Ord(tyInt64), Ord(Ass.Expr.ResolvedType.Kind));
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Gap 2: environment and process                                        }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_GetEnvVar_ReturnsString;
begin
  SemanticOK(SrcGetEnvVar);
end;

procedure TSelfHostingTests.TestSemantic_Exec_ReturnsInteger;
begin
  SemanticOK(SrcExec);
end;

procedure TSelfHostingTests.TestSemantic_Halt_OK;
begin
  SemanticOK(SrcHalt);
end;

procedure TSelfHostingTests.TestSemantic_GetEnvironmentVariable_ReturnsString;
begin
  SemanticOK(SrcGetEnvironmentVariable);
end;

{ ------------------------------------------------------------------ }
{ Step 11: file path manipulation                                     }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_ChangeFileExt_ReturnsString;
begin
  SemanticOK(SrcChangeFileExt);
end;

procedure TSelfHostingTests.TestSemantic_ExtractFileName_ReturnsString;
begin
  SemanticOK(SrcExtractFileName);
end;

procedure TSelfHostingTests.TestSemantic_ExtractFilePath_ReturnsString;
begin
  SemanticOK(SrcExtractFilePath);
end;

procedure TSelfHostingTests.TestSemantic_IncludeTrailingPathDelimiter_ReturnsString;
begin
  SemanticOK(SrcIncludeTrailingPathDelimiter);
end;

{ ------------------------------------------------------------------ }
{ MaxInt built-in constant                                            }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_MaxInt_ResolvesToInt64;
begin
  SemanticOK(SrcMaxInt);
end;

initialization
  RegisterTest(TSelfHostingTests);

end.
