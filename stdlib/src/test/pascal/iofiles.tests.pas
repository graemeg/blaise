{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for IO.Files: the recursive FindFiles walker (glob and predicate
  overloads) and the MatchGlob name matcher.  Each test builds its own tree
  under the temp directory in SetUp and removes it in TearDown.

  Fixture layout (FRoot):

    a.pas  b.pas  notes.txt  z.inc
    empty/
    sub/c.pas
    sub/deeper/d.pas

  Self-registers via the initialization section. }

unit IOFiles.Tests;

interface

uses
  blaise.testing, SysUtils, Generics.Collections, IO.Files;

type
  TIOFilesTests = class(TTestCase)
  private
    FRoot: string;
    procedure Touch(const ARelPath: string);
    procedure SymLink(const ATarget, ARelLink: string);
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestGlob_RecursiveInLexicalOrder;
    procedure TestGlob_ExcludesNonMatching;
    procedure TestGlob_StarMatchesEveryFile;
    procedure TestGlob_QuestionMarkIsOneChar;
    procedure TestGlob_NoMatchGivesEmptyList;
    procedure TestPredicate_ArrowLambda;
    procedure TestPredicate_ReceivesRootJoinedPath;
    procedure TestEmptyDirectoryGivesEmptyList;
    procedure TestTrailingSlashOnRootIsIgnored;
    procedure TestMissingRootRaises;
    procedure TestRootThatIsAFileRaises;
    procedure TestEmptyRootRaises;
    procedure TestSymlinkedDirectoryIsNotFollowed;
    procedure TestSymlinkCycleTerminates;
    procedure TestSymlinkedFileIsReturned;
    procedure TestMatchGlob_Literal;
    procedure TestMatchGlob_Star;
    procedure TestMatchGlob_QuestionMark;
    procedure TestMatchGlob_IsCaseSensitive;
  end;

implementation

procedure TIOFilesTests.Touch(const ARelPath: string);
begin
  WriteFile(FRoot + '/' + ARelPath, 'x');
end;

procedure TIOFilesTests.SymLink(const ATarget, ARelLink: string);
begin
  Exec('ln -s ''' + ATarget + ''' ''' + FRoot + '/' + ARelLink + '''');
end;

procedure TIOFilesTests.SetUp;
begin
  FRoot := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-iofiles-' +
    IntToStr(GetProcessID());
  Exec('rm -rf ''' + FRoot + '''');
  ForceDirectories(FRoot + '/sub/deeper');
  ForceDirectories(FRoot + '/empty');
  Touch('b.pas');
  Touch('a.pas');
  Touch('notes.txt');
  Touch('z.inc');
  Touch('sub/c.pas');
  Touch('sub/deeper/d.pas');
end;

procedure TIOFilesTests.TearDown;
begin
  Exec('rm -rf ''' + FRoot + '''');
end;

procedure TIOFilesTests.TestGlob_RecursiveInLexicalOrder;
var
  L: TList<string>;
begin
  { Depth-first, each directory's entries in byte order: the result must not
    depend on the order the file system happens to list them in. }
  L := FindFiles(FRoot, '*.pas');
  AssertEquals('count', 4, Int32(L.Count));
  AssertEquals('0', FRoot + '/a.pas', L[0]);
  AssertEquals('1', FRoot + '/b.pas', L[1]);
  AssertEquals('2', FRoot + '/sub/c.pas', L[2]);
  AssertEquals('3', FRoot + '/sub/deeper/d.pas', L[3]);
end;

procedure TIOFilesTests.TestGlob_ExcludesNonMatching;
var
  L: TList<string>;
begin
  L := FindFiles(FRoot, '*.txt');
  AssertEquals('count', 1, Int32(L.Count));
  AssertEquals('0', FRoot + '/notes.txt', L[0]);
end;

procedure TIOFilesTests.TestGlob_StarMatchesEveryFile;
var
  L: TList<string>;
begin
  { Directories are walked, never returned. }
  L := FindFiles(FRoot, '*');
  AssertEquals('count', 6, Int32(L.Count));
  AssertEquals('last', FRoot + '/z.inc', L[5]);
end;

procedure TIOFilesTests.TestGlob_QuestionMarkIsOneChar;
begin
  AssertEquals('?.pas', 4, Int32(FindFiles(FRoot, '?.pas').Count));
  AssertEquals('??.pas', 0, Int32(FindFiles(FRoot, '??.pas').Count));
end;

procedure TIOFilesTests.TestGlob_NoMatchGivesEmptyList;
var
  L: TList<string>;
begin
  L := FindFiles(FRoot, '*.pp');
  AssertNotNull('list', L);
  AssertEquals('count', 0, Int32(L.Count));
end;

procedure TIOFilesTests.TestPredicate_ArrowLambda;
var
  L: TList<string>;
begin
  L := FindFiles(FRoot, P -> Pos('/sub/', P) >= 0);
  AssertEquals('count', 2, Int32(L.Count));
  AssertEquals('0', FRoot + '/sub/c.pas', L[0]);
  AssertEquals('1', FRoot + '/sub/deeper/d.pas', L[1]);
end;

procedure TIOFilesTests.TestPredicate_ReceivesRootJoinedPath;
var
  Seen: TList<string>;
  L: TList<string>;
begin
  Seen := TList<string>.Create();
  L := FindFiles(FRoot,
    function(P: string): Boolean
    begin
      Seen.Add(P);
      Result := False;
    end);
  AssertEquals('none accepted', 0, Int32(L.Count));
  AssertEquals('every file offered', 6, Int32(Seen.Count));
  AssertEquals('first', FRoot + '/a.pas', Seen[0]);
end;

procedure TIOFilesTests.TestEmptyDirectoryGivesEmptyList;
begin
  AssertEquals('count', 0, Int32(FindFiles(FRoot + '/empty', '*').Count));
end;

procedure TIOFilesTests.TestTrailingSlashOnRootIsIgnored;
var
  L: TList<string>;
begin
  L := FindFiles(FRoot + '/', '*.txt');
  AssertEquals('count', 1, Int32(L.Count));
  AssertEquals('0', FRoot + '/notes.txt', L[0]);
end;

procedure TIOFilesTests.TestMissingRootRaises;
var
  Root: string;
begin
  { A root that is not there is a caller error, not an empty result: an
    analyser that silently reports "0 issues" for a mistyped path is worse
    than one that stops. }
  Root := FRoot + '/no-such-dir';
  AssertRaises('EDirectoryNotFound',
    procedure
    begin
      FindFiles(Root, '*');
    end);
end;

procedure TIOFilesTests.TestRootThatIsAFileRaises;
var
  Root: string;
begin
  Root := FRoot + '/a.pas';
  AssertRaises('EDirectoryNotFound',
    procedure
    begin
      FindFiles(Root, '*');
    end);
end;

procedure TIOFilesTests.TestEmptyRootRaises;
begin
  { '' is not silently taken to mean the current directory -- callers that
    want that pass '.'. }
  AssertRaises('EDirectoryNotFound',
    procedure
    begin
      FindFiles('', '*');
    end);
end;

procedure TIOFilesTests.TestSymlinkedDirectoryIsNotFollowed;
var
  L: TList<string>;
begin
  SymLink(FRoot + '/sub', 'linked');
  L := FindFiles(FRoot, '*.pas');
  AssertEquals('count', 4, Int32(L.Count));
end;

procedure TIOFilesTests.TestSymlinkCycleTerminates;
var
  L: TList<string>;
begin
  { Followed, this link would recurse forever. }
  SymLink(FRoot, 'sub/loop');
  L := FindFiles(FRoot, '*.pas');
  AssertEquals('count', 4, Int32(L.Count));
end;

procedure TIOFilesTests.TestSymlinkedFileIsReturned;
var
  L: TList<string>;
begin
  SymLink(FRoot + '/a.pas', 'alias.pas');
  L := FindFiles(FRoot, '*.pas');
  AssertEquals('count', 5, Int32(L.Count));
  AssertEquals('1', FRoot + '/alias.pas', L[1]);
end;

procedure TIOFilesTests.TestMatchGlob_Literal;
begin
  AssertTrue('same', MatchGlob('a.pas', 'a.pas'));
  AssertFalse('different', MatchGlob('a.pas', 'b.pas'));
  AssertFalse('prefix only', MatchGlob('a.pas', 'a.pa'));
  AssertTrue('both empty', MatchGlob('', ''));
end;

procedure TIOFilesTests.TestMatchGlob_Star;
begin
  AssertTrue('suffix', MatchGlob('a.pas', '*.pas'));
  AssertFalse('suffix must end', MatchGlob('a.pas.bak', '*.pas'));
  AssertTrue('star matches empty', MatchGlob('.pas', '*.pas'));
  AssertTrue('star alone', MatchGlob('anything', '*'));
  AssertTrue('star on empty', MatchGlob('', '*'));
  AssertTrue('several stars', MatchGlob('abXcdYef', 'ab*cd*ef'));
  AssertFalse('several stars, miss', MatchGlob('abXcdYeg', 'ab*cd*ef'));
  AssertTrue('backtracks', MatchGlob('aaab', '*ab'));
end;

procedure TIOFilesTests.TestMatchGlob_QuestionMark;
begin
  AssertTrue('one char', MatchGlob('a.pas', '?.pas'));
  AssertFalse('not zero chars', MatchGlob('.pas', '?.pas'));
  AssertFalse('not two chars', MatchGlob('ab.pas', '?.pas'));
end;

procedure TIOFilesTests.TestMatchGlob_IsCaseSensitive;
begin
  { Unix file names are case-sensitive; see the IO.Files unit notes. }
  AssertFalse('case', MatchGlob('A.PAS', '*.pas'));
end;

initialization
  RegisterTest(TIOFilesTests);

end.
