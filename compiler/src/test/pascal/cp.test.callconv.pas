{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit cp.test.callconv;

{ The calling convention as part of a procedural type
  (windows-x86_64-backend-design.adoc, "Language rule: calling convention is
  part of the type"; language-rationale.adoc, "Calling-Convention
  Directives").

    type TCallback = function(X: Int32): Int32; cdecl;

  A routine is of the C convention when it is declared cdecl or binds a
  named library (external '<lib>').  Giving a value of one convention to a
  procedural type of the other is an error on a target where the two
  conventions differ (windows-x86_64) and a portability warning on every
  other target, where they coincide. }

interface

uses
  SysUtils, blaise.testing, cp.test.harness, uAST, uParser, uLexer;

type
  TCallConvTests = class(TTestCase)
  private
    function TypeDefOf(const ASrc, AName: string): TProceduralTypeDef;
    function ParseErr(const ASrc: string): string;
    procedure AssertClean(const ASrc: string);
    procedure AssertMismatch(const ASrc: string);
  published
    { the directive after the signature, with or without the semicolon }
    procedure TestParse_CdeclAfterSemicolon;
    procedure TestParse_CdeclWithoutSemicolon;
    procedure TestParse_NoDirective_DefaultConvention;
    { only cdecl: the removed directives keep their D5 message }
    procedure TestParse_StdcallOnProcType_Rejected;
    { a method pointer or a closure has a receiver or an environment no C
      caller supplies }
    procedure TestParse_OfObjectCdecl_Rejected;
    procedure TestParse_ReferenceToCdecl_Rejected;
    { a variable or field that happens to be called cdecl is not the
      directive }
    procedure TestParse_FieldNamedCdecl_AfterProcType;
    procedure TestParse_InlineProcType_CarriesCdecl;

    { the rule }
    procedure TestDefaultRoutineToCdeclType_ErrorOnWindows;
    procedure TestDefaultRoutineToCdeclType_WarnsElsewhere;
    procedure TestCdeclRoutineToDefaultType_ErrorOnWindows;
    procedure TestCdeclRoutineToCdeclType_Clean;
    procedure TestDefaultRoutineToDefaultType_Clean;
    procedure TestLibraryExternal_IsCConvention;
    procedure TestLibraryLessExternal_IsDefaultConvention;
    procedure TestProcTypeToProcType_Mismatch;
    procedure TestArgument_Mismatch;
    procedure TestMethodArgument_Mismatch;
    procedure TestReferenceToTarget_AnyConvention;
    procedure TestInlineCdeclType_Matches;
    procedure TestGenericProcTypeCdecl_Matches;
    procedure TestNil_IsAnyConvention;
  end;

implementation

const
  WIN = 'windows-x86_64';
  LINUX = 'linux-x86_64';
  MAC = 'macos-arm64';

function TCallConvTests.TypeDefOf(const ASrc, AName: string): TProceduralTypeDef;
var
  Prog: TProgram;
  I: Int;
  TD: TTypeDecl;
begin
  Result := nil;
  Prog := ParseProgram(ASrc);
  try
    for I := 0 to Prog.Block.TypeDecls.Count - 1 do
    begin
      TD := TTypeDecl(Prog.Block.TypeDecls.Items[I]);
      if SameText(TD.Name, AName) and (TD.Def is TProceduralTypeDef) then
      begin
        { detach the def so it outlives the program }
        Result := TProceduralTypeDef(TD.Def);
        TD.Def := nil;
      end;
    end;
  finally
    Prog.Free();
  end;
  AssertTrue('procedural type ' + AName + ' parsed', Result <> nil);
end;

function TCallConvTests.ParseErr(const ASrc: string): string;
var
  Prog: TProgram;
begin
  Result := '';
  try
    Prog := ParseProgram(ASrc);
    Prog.Free();
  except
    on E: EParseError do
      Result := E.Message;
  end;
end;

procedure TCallConvTests.AssertClean(const ASrc: string);
begin
  AssertEquals('no error on Windows', '', SemanticErrorOn(ASrc, WIN));
  AssertEquals('no error on Linux', '', SemanticErrorOn(ASrc, LINUX));
  AssertEquals('no warning on Linux', '',
    Trim(SemanticWarningsOn(ASrc, LINUX)));
  AssertEquals('no warning on macOS', '', Trim(SemanticWarningsOn(ASrc, MAC)));
end;

procedure TCallConvTests.AssertMismatch(const ASrc: string);
var
  Msg: string;
begin
  Msg := SemanticErrorOn(ASrc, WIN);
  AssertTrue('an error on Windows, got: ' + Msg,
    Pos('calling convention', Msg) >= 0);
  AssertEquals('no error on Linux', '', SemanticErrorOn(ASrc, LINUX));
  Msg := SemanticWarningsOn(ASrc, LINUX);
  AssertTrue('a portability warning on Linux, got: ' + Msg,
    (Pos('calling convention', Msg) >= 0) and (Pos(WIN, Msg) >= 0));
  Msg := SemanticWarningsOn(ASrc, MAC);
  AssertTrue('a portability warning on macOS, got: ' + Msg,
    Pos('calling convention', Msg) >= 0);
end;

procedure TCallConvTests.TestParse_CdeclAfterSemicolon;
var
  Def: TProceduralTypeDef;
begin
  Def := TypeDefOf('program P; type TCb = function(X: Int32): Int32; cdecl; ' +
    'begin end.', 'TCb');
  try
    AssertEquals('cdecl', 'cdecl', Def.CallingConv);
  finally
    Def.Free();
  end;
end;

procedure TCallConvTests.TestParse_CdeclWithoutSemicolon;
var
  Def: TProceduralTypeDef;
begin
  Def := TypeDefOf('program P; type TCb = procedure(X: Int32) cdecl; ' +
    'begin end.', 'TCb');
  try
    AssertEquals('cdecl', 'cdecl', Def.CallingConv);
  finally
    Def.Free();
  end;
end;

procedure TCallConvTests.TestParse_NoDirective_DefaultConvention;
var
  Def: TProceduralTypeDef;
begin
  Def := TypeDefOf('program P; type TCb = function(X: Int32): Int32; ' +
    'begin end.', 'TCb');
  try
    AssertEquals('default', '', Def.CallingConv);
  finally
    Def.Free();
  end;
end;

procedure TCallConvTests.TestParse_StdcallOnProcType_Rejected;
var
  Msg: string;
begin
  Msg := ParseErr('program P; type TCb = procedure(X: Int32); stdcall; ' +
    'begin end.');
  AssertTrue('the D5 message, got: ' + Msg,
    Pos('''stdcall'' is not supported in Blaise', Msg) >= 0);
end;

procedure TCallConvTests.TestParse_OfObjectCdecl_Rejected;
var
  Msg: string;
begin
  Msg := ParseErr('program P; type TEv = procedure(X: Int32) of object; ' +
    'cdecl; begin end.');
  AssertTrue('rejected, got: ' + Msg, Pos('''of object''', Msg) >= 0);
end;

procedure TCallConvTests.TestParse_ReferenceToCdecl_Rejected;
var
  Msg: string;
begin
  Msg := ParseErr('program P; type TFn = reference to procedure(X: Int32); ' +
    'cdecl; begin end.');
  AssertTrue('rejected, got: ' + Msg, Pos('''reference to''', Msg) >= 0);
end;

procedure TCallConvTests.TestParse_FieldNamedCdecl_AfterProcType;
const
  SRC = 'program P; type TR = record F: procedure; cdecl: Int32; end; ' +
    'var V: procedure; cdecl, X: Int32; begin end.';
begin
  AssertEquals('parses', '', ParseErr(SRC));
  AssertEquals('analyses', '', SemanticError(SRC));
end;

procedure TCallConvTests.TestParse_InlineProcType_CarriesCdecl;
var
  Prog: TProgram;
  VD: TVarDecl;
begin
  Prog := ParseProgram('program P; var F: function(X: Int32): Int32; cdecl; ' +
    'begin end.');
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertTrue('the encoded type carries cdecl, got: ' + VD.TypeName,
      Pos('cdecl', VD.TypeName) >= 0);
  finally
    Prog.Free();
  end;
end;

procedure TCallConvTests.TestDefaultRoutineToCdeclType_ErrorOnWindows;
var
  Msg: string;
begin
  Msg := SemanticErrorOn('program P; type TCb = function(X: Int32): Int32; ' +
    'cdecl; function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var F: TCb; begin F := @Twice; end.', WIN);
  AssertTrue('names the convention, got: ' + Msg,
    Pos('calling convention', Msg) >= 0);
  AssertTrue('names the type, got: ' + Msg, Pos('TCb', Msg) >= 0);
  AssertTrue('names the routine, got: ' + Msg, Pos('Twice', Msg) >= 0);
  AssertTrue('says what to write, got: ' + Msg, Pos('cdecl', Msg) >= 0);
end;

procedure TCallConvTests.TestDefaultRoutineToCdeclType_WarnsElsewhere;
begin
  AssertMismatch('program P; type TCb = function(X: Int32): Int32; cdecl; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var F: TCb; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestCdeclRoutineToDefaultType_ErrorOnWindows;
begin
  AssertMismatch('program P; type TFn = function(X: Int32): Int32; ' +
    'function Twice(X: Int32): Int32; cdecl; begin Result := X * 2; end; ' +
    'var F: TFn; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestCdeclRoutineToCdeclType_Clean;
begin
  AssertClean('program P; type TCb = function(X: Int32): Int32; cdecl; ' +
    'function Twice(X: Int32): Int32; cdecl; begin Result := X * 2; end; ' +
    'var F: TCb; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestDefaultRoutineToDefaultType_Clean;
begin
  AssertClean('program P; type TFn = function(X: Int32): Int32; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var F: TFn; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestLibraryExternal_IsCConvention;
begin
  AssertClean('program P; type TPuts = function(S: PChar): Int32; cdecl; ' +
    'function puts(S: PChar): Int32; external ''c'' name ''puts''; ' +
    'var F: TPuts; begin F := @puts; end.');
  AssertMismatch('program P; type TPuts = function(S: PChar): Int32; ' +
    'function puts(S: PChar): Int32; external ''c'' name ''puts''; ' +
    'var F: TPuts; begin F := @puts; end.');
end;

procedure TCallConvTests.TestLibraryLessExternal_IsDefaultConvention;
begin
  AssertClean('program P; type TLen = function(S: PChar): Int; ' +
    'function _StrLenZ(S: PChar): Int; external name ''_StrLenZ''; ' +
    'var F: TLen; begin F := @_StrLenZ; end.');
end;

procedure TCallConvTests.TestProcTypeToProcType_Mismatch;
begin
  AssertMismatch('program P; type TCb = procedure(X: Int32); cdecl; ' +
    'TFn = procedure(X: Int32); var A: TCb; B: TFn; begin A := B; end.');
end;

procedure TCallConvTests.TestArgument_Mismatch;
begin
  AssertMismatch('program P; type TCb = function(X: Int32): Int32; cdecl; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'procedure Take(F: TCb); begin end; begin Take(@Twice); end.');
end;

procedure TCallConvTests.TestMethodArgument_Mismatch;
begin
  AssertMismatch('program P; type TCb = function(X: Int32): Int32; cdecl; ' +
    'TC = class procedure Take(F: TCb); end; ' +
    'procedure TC.Take(F: TCb); begin end; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var C: TC; begin C := TC.Create(); C.Take(@Twice); end.');
end;

procedure TCallConvTests.TestReferenceToTarget_AnyConvention;
begin
  { a closure is called the Blaise way; the adapter calls the routine in
    its own convention }
  AssertClean('program P; type TFn = reference to function(X: Int32): Int32; ' +
    'function Twice(X: Int32): Int32; cdecl; begin Result := X * 2; end; ' +
    'var F: TFn; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestInlineCdeclType_Matches;
begin
  AssertClean('program P; ' +
    'function Twice(X: Int32): Int32; cdecl; begin Result := X * 2; end; ' +
    'var F: function(X: Int32): Int32; cdecl; begin F := @Twice; end.');
  AssertMismatch('program P; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var F: function(X: Int32): Int32; cdecl; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestGenericProcTypeCdecl_Matches;
begin
  AssertClean('program P; type TFn<T> = function(X: T): T; cdecl; ' +
    'function Twice(X: Int32): Int32; cdecl; begin Result := X * 2; end; ' +
    'var F: TFn<Int32>; begin F := @Twice; end.');
  AssertMismatch('program P; type TFn<T> = function(X: T): T; cdecl; ' +
    'function Twice(X: Int32): Int32; begin Result := X * 2; end; ' +
    'var F: TFn<Int32>; begin F := @Twice; end.');
end;

procedure TCallConvTests.TestNil_IsAnyConvention;
begin
  AssertClean('program P; type TCb = procedure(X: Int32); cdecl; ' +
    'var F: TCb; begin F := nil; end.');
end;

initialization
  RegisterTest(TCallConvTests);

end.
