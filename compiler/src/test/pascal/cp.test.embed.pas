{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.embed;

(* IR-level tests for the compile-time file-embedding directives, EMBED
   (byte array) and EMBEDSTR (string).

   Both are expanded by the LEXER into the tokens a hand-written constant
   initialiser would have produced, so the parser, semantic pass and both
   backends see nothing new.  These tests assert the expansion is correct
   (element count, element values, exact string bytes) and that the failure
   modes are compile-time errors rather than silent wrong data.

   Design: docs/embedded-resources-design.adoc *)

interface

uses
  Classes, SysUtils, Streams, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uUnitInterfaceIO, blaise.codegen.qbe;

type
  TEmbedTests = class(TTestCase)
  private
    FDir: string;
    { Write AContent to <tmp>/AName and return the full path. }
    function  WriteFixture(const AName, AContent: string): string;
    { Parse ASrc as if it lived in <tmp>/prog.pas, so a relative embed
      path resolves against the fixture directory. }
    function  ParseAt(const ASrc: string): TProgram;
    function  GenIRAt(const ASrc: string): string;
    function  IRContains(const AIR, AFragment: string): Boolean;
    { Compile ASrc expecting a failure; return the message ('' on success). }
    function  ExpectError(const ASrc: string): string;
  public
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { --- EMBED: byte arrays --- }
    procedure TestEmbed_ElementCountMatchesFileSize;
    procedure TestEmbed_ElementValuesAreFileBytes;
    procedure TestEmbed_HighByteIsUnsigned;
    procedure TestEmbed_EmptyFileYieldsEmptyArray;
    procedure TestEmbed_BinaryBytesIncludingNulAndNewline;
    procedure TestEmbed_ReachesIRAsData;

    { --- EMBEDSTR: strings --- }
    procedure TestEmbedStr_ExactBytes;
    procedure TestEmbedStr_NoNewlineTranslation;
    procedure TestEmbedStr_EmptyFile;
    procedure TestEmbedStr_ReachesIRAsData;

    { --- path resolution --- }
    procedure TestEmbed_PathIsRelativeToSourceFile;
    procedure TestEmbed_SubdirectoryPath;
    procedure TestEmbed_PathIsCaseSensitiveNotUpperCased;

    { --- failure modes --- }
    procedure TestEmbed_MissingFileIsCompileError;
    procedure TestEmbedStr_MissingFileIsCompileError;
    procedure TestEmbed_ErrorNamesTheMissingPath;

    { --- interaction with conditional compilation --- }
    procedure TestEmbed_InSkippedIfdefBranchIsNotRead;
    procedure TestEmbed_InTakenIfdefBranchIsRead;

    { --- unit-cache staleness key --- }
    procedure TestCacheKey_ChangesWhenEmbeddedFileChanges;
    procedure TestCacheKey_StableWhenNothingChanges;
    procedure TestCacheKey_ChangesWhenEmbeddedPathChanges;
    procedure TestCacheKey_CoversDefineGatedEmbed;
    procedure TestLexer_RecordsEmbeddedFiles;
  end;

implementation

const
  LE = #10;

procedure TEmbedTests.SetUp;
begin
  { A per-suite scratch directory.  Tests write their own fixtures so the
    suite carries no binary files in the repository. }
  FDir := '/tmp/blaise-embed-tests';
  if not DirectoryExists(FDir) then
    ForceDirectories(FDir);
end;

procedure TEmbedTests.TearDown;
begin
  { Fixtures are small and overwritten per test; leaving them costs nothing
    and keeps a failed run inspectable. }
end;

function TEmbedTests.WriteFixture(const AName, AContent: string): string;
var
  F: TFileOutputStream;
  P: string;
begin
  P := FDir + '/' + AName;
  F := TFileOutputStream.Create(P);
  try
    if Length(AContent) > 0 then
      F.Write(PChar(AContent), Length(AContent));
  finally
    F.Close();
    F.Free();
  end;
  Result := P;
end;

function TEmbedTests.ParseAt(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc, FDir + '/prog.pas');
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TEmbedTests.GenIRAt(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc, FDir + '/prog.pas');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TEmbedTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) >= 0;
end;

function TEmbedTests.ExpectError(const ASrc: string): string;
var
  Pr: TProgram;
begin
  Result := '';
  try
    Pr := ParseAt(ASrc);
    Pr.Free();
  except
    on E: Exception do
      Result := E.Message;
  end;
end;

{ ------------------------------------------------------------------ }
{ EMBED — byte arrays                                                  }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestEmbed_ElementCountMatchesFileSize;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  WriteFixture('five.bin', 'ABCDE');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'five.bin'};
    begin end.
    ''');
  AssertNotNull('program parsed', Pr);
  AssertEquals('one const decl', 1, Pr.Block.ConstDecls.Count);
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertTrue('is array const', CD.IsArrayConst);
  AssertEquals('element count = file size', 5, CD.ArrayElements.Count);
  AssertEquals('low bound', 0, CD.ArrayLowBound);
  AssertEquals('high bound', 4, CD.ArrayHighBound);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_ElementValuesAreFileBytes;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { 'AB' = 65, 66 }
  WriteFixture('ab.bin', 'AB');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'ab.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('two elements', 2, CD.ArrayElements.Count);
  AssertEquals('byte 0 is 65', '65', CD.ArrayElements.Strings[0]);
  AssertEquals('byte 1 is 66', '66', CD.ArrayElements.Strings[1]);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_HighByteIsUnsigned;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { A byte above 127 must expand as 0..255, not a negative number -- the
    classic signed-char bug when converting bytes to source text. }
  WriteFixture('high.bin', Chr(200) + Chr(255));
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'high.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('two elements', 2, CD.ArrayElements.Count);
  AssertEquals('byte 0 is 200', '200', CD.ArrayElements.Strings[0]);
  AssertEquals('byte 1 is 255', '255', CD.ArrayElements.Strings[1]);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_EmptyFileYieldsEmptyArray;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  WriteFixture('empty.bin', '');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'empty.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('no elements', 0, CD.ArrayElements.Count);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_BinaryBytesIncludingNulAndNewline;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { Genuinely binary content: a NUL, a newline, and a quote -- none of these
    may terminate the expansion early or be escaped away. }
  WriteFixture('bin.dat', Chr(0) + Chr(10) + Chr(39) + Chr(13));
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'bin.dat'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('four elements', 4, CD.ArrayElements.Count);
  AssertEquals('NUL', '0', CD.ArrayElements.Strings[0]);
  AssertEquals('LF', '10', CD.ArrayElements.Strings[1]);
  AssertEquals('quote', '39', CD.ArrayElements.Strings[2]);
  AssertEquals('CR', '13', CD.ArrayElements.Strings[3]);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_ReachesIRAsData;
var
  IR: string;
begin
  WriteFixture('ir.bin', 'AB');
  IR := GenIRAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'ir.bin'};
    var X: Byte;
    begin X := B[0]; WriteLn(X) end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { The bytes must reach the data section as byte items. }
  AssertTrue('emits byte 65', IRContains(IR, '65'));
  AssertTrue('emits byte 66', IRContains(IR, '66'));
end;

{ ------------------------------------------------------------------ }
{ EMBEDSTR — strings                                                   }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestEmbedStr_ExactBytes;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  WriteFixture('hello.txt', 'Hello');
  Pr := ParseAt(
    '''
    program P;
    const S: string = {$EMBEDSTR 'hello.txt'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertTrue('is string const', CD.IsString);
  AssertEquals('exact content', 'Hello', CD.StrVal);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbedStr_NoNewlineTranslation;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { CRLF must survive verbatim -- no newline translation, no trailing-newline
    trimming (TStringList round-tripping would silently do both). }
  WriteFixture('crlf.txt', 'a' + Chr(13) + Chr(10) + 'b' + Chr(10));
  Pr := ParseAt(
    '''
    program P;
    const S: string = {$EMBEDSTR 'crlf.txt'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('length preserved', 5, Length(CD.StrVal));
  AssertEquals('CR at 1', 13, Ord(CD.StrVal[1]));
  AssertEquals('LF at 2', 10, Ord(CD.StrVal[2]));
  AssertEquals('trailing LF kept', 10, Ord(CD.StrVal[4]));
  Pr.Free();
end;

procedure TEmbedTests.TestEmbedStr_EmptyFile;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  WriteFixture('empty.txt', '');
  Pr := ParseAt(
    '''
    program P;
    const S: string = {$EMBEDSTR 'empty.txt'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertTrue('is string const', CD.IsString);
  AssertEquals('empty', '', CD.StrVal);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbedStr_ReachesIRAsData;
var
  IR: string;
begin
  WriteFixture('greet.txt', 'Hi');
  IR := GenIRAt(
    '''
    program P;
    const S: string = {$EMBEDSTR 'greet.txt'};
    begin WriteLn(S) end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('string bytes in data', IRContains(IR, 'Hi'));
end;

{ ------------------------------------------------------------------ }
{ Path resolution                                                      }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestEmbed_PathIsRelativeToSourceFile;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { The fixture sits beside the (notional) source file, NOT in the process
    CWD -- which is the project root when the suite runs.  Resolving against
    CWD would fail to find it. }
  WriteFixture('beside.bin', 'XY');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'beside.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('found beside the source', 2, CD.ArrayElements.Count);
  AssertEquals('byte 0', '88', CD.ArrayElements.Strings[0]);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_SubdirectoryPath;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  if not DirectoryExists(FDir + '/assets') then
    ForceDirectories(FDir + '/assets');
  WriteFixture('assets/nested.bin', 'Z');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'assets/nested.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('one byte', 1, CD.ArrayElements.Count);
  AssertEquals('byte 0 is Z', '90', CD.ArrayElements.Strings[0]);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_PathIsCaseSensitiveNotUpperCased;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { The existing DirectiveArg helper upper-cases its result, which is right
    for IFDEF but would turn 'MixedCase.bin' into 'MIXEDCASE.BIN' and fail
    to open it on a case-sensitive filesystem. }
  WriteFixture('MixedCase.bin', 'Q');
  Pr := ParseAt(
    '''
    program P;
    const B: array of Byte = {$EMBED 'MixedCase.bin'};
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('one byte', 1, CD.ArrayElements.Count);
  AssertEquals('byte 0 is Q', '81', CD.ArrayElements.Strings[0]);
  Pr.Free();
end;

{ ------------------------------------------------------------------ }
{ Failure modes                                                        }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestEmbed_MissingFileIsCompileError;
var
  Msg: string;
begin
  Msg := ExpectError(
    '''
    program P;
    const B: array of Byte = {$EMBED 'does-not-exist.bin'};
    begin end.
    ''');
  AssertTrue('missing file is an error', Msg <> '');
end;

procedure TEmbedTests.TestEmbedStr_MissingFileIsCompileError;
var
  Msg: string;
begin
  Msg := ExpectError(
    '''
    program P;
    const S: string = {$EMBEDSTR 'no-such.txt'};
    begin end.
    ''');
  AssertTrue('missing file is an error', Msg <> '');
end;

procedure TEmbedTests.TestEmbed_ErrorNamesTheMissingPath;
var
  Msg: string;
begin
  { A resource that is not there must fail the build with a message that
    names it -- that is the whole trade against a runtime-lookup model. }
  Msg := ExpectError(
    '''
    program P;
    const B: array of Byte = {$EMBED 'ghost-asset.png'};
    begin end.
    ''');
  AssertTrue('error mentions the path',
             Pos('ghost-asset.png', Msg) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Conditional compilation                                              }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestEmbed_InSkippedIfdefBranchIsNotRead;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { A directive inside a branch that is being SKIPPED must not read its file.
    Otherwise an asset that only exists in one build configuration would
    break every other configuration -- and the skip path would need the file
    present merely to throw the tokens away. }
  WriteFixture('taken.txt', 'TAKEN');
  Pr := ParseAt(
    '''
    program P;
    const
    {$IFDEF NOT_DEFINED_ANYWHERE}
      S: string = {$EMBEDSTR 'this-file-does-not-exist.txt'};
    {$ELSE}
      S: string = {$EMBEDSTR 'taken.txt'};
    {$ENDIF}
    begin end.
    ''');
  AssertNotNull('program parsed despite the missing file', Pr);
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('the taken branch supplied the value', 'TAKEN', CD.StrVal);
  Pr.Free();
end;

procedure TEmbedTests.TestEmbed_InTakenIfdefBranchIsRead;
var
  Pr: TProgram;
  CD: TConstDecl;
begin
  { The other direction: inside a branch that IS taken, the directive expands
    normally.  Guards against a fix for the skip case disabling it wholesale. }
  WriteFixture('cond.txt', 'CONDITIONAL');
  Pr := ParseAt(
    '''
    program P;
    const
    {$IFDEF BLAISE}
      S: string = {$EMBEDSTR 'cond.txt'};
    {$ENDIF}
    begin end.
    ''');
  CD := TConstDecl(Pr.Block.ConstDecls.Items[0]);
  AssertEquals('expanded in the taken branch', 'CONDITIONAL', CD.StrVal);
  Pr.Free();
end;

{ ------------------------------------------------------------------ }
{ Unit-cache staleness key                                             }
{ ------------------------------------------------------------------ }

procedure TEmbedTests.TestCacheKey_ChangesWhenEmbeddedFileChanges;
var
  Src, H1, H2: string;
begin
  { The regression this design is most exposed to: hashing only the .pas
    would let an asset change slip past the cache, and the rebuilt binary
    would silently carry the previous bytes -- exactly the failure mode the
    feature exists to remove.  No other test layer would catch it. }
  Src :=
    '''
    unit U;
    interface
    const S: string = {$EMBEDSTR 'cachekey.txt'};
    implementation
    end.
    ''';
  WriteFixture('cachekey.txt', 'ONE');
  H1 := SourceHashWithEmbeds(Src, FDir + '/u.pas', nil);
  WriteFixture('cachekey.txt', 'TWO');
  H2 := SourceHashWithEmbeds(Src, FDir + '/u.pas', nil);
  AssertTrue('hash covers embedded content', H1 <> H2);
end;

procedure TEmbedTests.TestCacheKey_StableWhenNothingChanges;
var
  Src, H1, H2: string;
begin
  { The other half: an unchanged asset must NOT invalidate, or every build
    recompiles everything and the cache is worthless. }
  Src :=
    '''
    unit U;
    interface
    const S: string = {$EMBEDSTR 'stable.txt'};
    implementation
    end.
    ''';
  WriteFixture('stable.txt', 'CONSTANT');
  H1 := SourceHashWithEmbeds(Src, FDir + '/u.pas', nil);
  H2 := SourceHashWithEmbeds(Src, FDir + '/u.pas', nil);
  AssertEquals('hash is stable', H1, H2);
end;

procedure TEmbedTests.TestCacheKey_ChangesWhenEmbeddedPathChanges;
var
  SrcA, SrcB, HA, HB: string;
begin
  { Two assets with IDENTICAL content but different names: swapping which
    one is embedded must still change the hash, otherwise a re-point to a
    different file would go unnoticed. }
  WriteFixture('same-a.txt', 'IDENTICAL');
  WriteFixture('same-b.txt', 'IDENTICAL');
  SrcA :=
    '''
    unit U;
    interface
    const S: string = {$EMBEDSTR 'same-a.txt'};
    implementation
    end.
    ''';
  SrcB :=
    '''
    unit U;
    interface
    const S: string = {$EMBEDSTR 'same-b.txt'};
    implementation
    end.
    ''';
  HA := SourceHashWithEmbeds(SrcA, FDir + '/u.pas', nil);
  HB := SourceHashWithEmbeds(SrcB, FDir + '/u.pas', nil);
  AssertTrue('hash covers the embedded path', HA <> HB);
end;

procedure TEmbedTests.TestCacheKey_CoversDefineGatedEmbed;
var
  Src, H1, H2: string;
  Defs:        TStringList;
begin
  { An embed behind an IFDEF is only discovered when the hash lexes with the
    SAME -d set the compile used.  Without the defines the discovery lex takes
    the ELSE branch, never sees the asset, and the cached .o survives an asset
    edit -- silently shipping the previous bytes.  That is the exact failure
    mode this hash exists to prevent, so it is worth its own test: the plain
    (define-less) cases above all pass even with the bug present. }
  Src :=
    '''
    unit U;
    interface
    {$IFDEF MYFEATURE}
    const S: string = {$EMBEDSTR 'gated.txt'};
    {$ELSE}
    const S: string = 'no-feature';
    {$ENDIF}
    implementation
    end.
    ''';
  Defs := TStringList.Create();
  try
    Defs.Add('MYFEATURE');
    WriteFixture('gated.txt', 'ONE');
    H1 := SourceHashWithEmbeds(Src, FDir + '/u.pas', Defs);
    WriteFixture('gated.txt', 'TWO');
    H2 := SourceHashWithEmbeds(Src, FDir + '/u.pas', Defs);
    AssertTrue('define-gated embed is in the cache key', H1 <> H2);
  finally
    Defs.Free();
  end;
end;

procedure TEmbedTests.TestLexer_RecordsEmbeddedFiles;
var
  L:   TLexer;
  Tok: TToken;
begin
  { The staleness key is built from what the lexer reports, so the reporting
    itself is worth pinning: every embedded file, resolved, recorded once. }
  WriteFixture('rec-one.txt', 'A');
  WriteFixture('rec-two.bin', 'B');
  L := TLexer.Create(
    '''
    unit U;
    interface
    const A: string = {$EMBEDSTR 'rec-one.txt'};
    const B: array of Byte = {$EMBED 'rec-two.bin'};
    implementation
    end.
    ''', FDir + '/u.pas');
  try
    repeat
      Tok := L.Next();
    until Tok.Kind = tkEOF;
    AssertEquals('two files recorded', 2, L.EmbeddedFiles.Count);
    AssertTrue('records the txt',
               Pos('rec-one.txt', L.EmbeddedFiles.Strings[0]) >= 0);
    AssertTrue('records the bin',
               Pos('rec-two.bin', L.EmbeddedFiles.Strings[1]) >= 0);
  finally
    L.Free();
  end;
end;

initialization
  RegisterTest(TEmbedTests);

end.
