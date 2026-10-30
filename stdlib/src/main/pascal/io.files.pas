{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ IO.Files - finding files on disk.

  FindFiles walks a directory tree and returns the files in it that match,
  in one call:

    Sources := FindFiles('src', '*.pas');
    Tests   := FindFiles('src', P -> Pos('/test/', P) >= 0);

  The first overload matches a glob against each file's NAME; the second
  hands each file's PATH to a predicate, so anything expressible as a test
  on a string -- a regex, a directory exclusion -- works without this unit
  knowing about it.

  Behaviour, shared by both overloads:

    * Recursive.  Directories are walked, never returned.
    * Deterministic: depth-first, each directory's entries in byte order
      (as Go's filepath.WalkDir), whatever order the file system lists them.
    * Paths are ARoot joined with the relative path, so a relative root
      gives relative paths.  A trailing separator on ARoot is ignored.
    * A missing root, a root that is not a directory, or an empty root
      raises EDirectoryNotFound -- a mistyped path must not look like an
      empty tree.  Pass '.' for the current directory.
    * A subdirectory that cannot be read is skipped.
    * Symbolic links: a link to a file is returned like a file; a link to a
      directory is NOT descended into (as find -P, Go, Rust walkdir), which
      also rules out link cycles.  The root itself is followed if it is a
      link, since the caller named it.
    * Only regular files are returned; FIFOs, sockets and devices are not.

  Not in SysUtils, where Delphi keeps its file helpers: the signatures need
  TList<string>, and Generics.Collections already uses SysUtils. }

unit IO.Files;

interface

uses
  SysUtils,
  Generics.Collections,
  Functional;

type
  { Raised by FindFiles when its root is not an existing directory. }
  EDirectoryNotFound = class(EInOutError)
  end;

{ The regular files under ARoot whose name matches the glob APattern (see
  MatchGlob).  Caller owns the list. }
function FindFiles(const ARoot, APattern: string): TList<string>; overload;

{ The regular files under ARoot whose path satisfies AMatch.  Caller owns the
  list. }
function FindFiles(const ARoot: string; AMatch: TPredicate<string>): TList<string>; overload;

{ True when AName matches the glob APattern: '*' matches any run of
  characters (including none), '?' exactly one, anything else itself.
  Case-sensitive, as Unix file names are.  No '[...]' classes and no '**':
  FindFiles is already recursive, and a predicate covers the rest. }
function MatchGlob(const AName, APattern: string): Boolean;

implementation

uses
  StrUtils;

{ Imported from the RTL (rtl.platform.posix): 0 missing, 1 regular file,
  2 directory, 3 symbolic link, 4 other.  FollowLinks <> 0 stats the link's
  target; 0 reports the link itself. }
function _PathKind(const Path: string; FollowLinks: Int32): Int32; external name '_PathKind';

const
  KIND_FILE    = 1;
  KIND_DIR     = 2;
  KIND_SYMLINK = 3;

  CH_STAR     = 42;  { '*' }
  CH_QUESTION = 63;  { '?' }
  CH_LF       = 10;

{ Iterative wildcard match with single-star backtracking: on a mismatch,
  retry from the most recent '*' with it absorbing one more character.
  Linear in practice, and no recursion for a pattern of many stars. }
function MatchGlob(const AName, APattern: string): Boolean;
var
  N, P: Int;
  StarP, StarN: Int;
  NLen, PLen: Int;
begin
  N := 0;
  P := 0;
  StarP := -1;
  StarN := 0;
  NLen := Length(AName);
  PLen := Length(APattern);
  while N < NLen do
  begin
    if (P < PLen) and (OrdAt(APattern, P) = CH_STAR) then
    begin
      StarP := P;
      StarN := N;
      P := P + 1;
    end
    else if (P < PLen) and ((OrdAt(APattern, P) = CH_QUESTION) or
                            (OrdAt(APattern, P) = OrdAt(AName, N))) then
    begin
      P := P + 1;
      N := N + 1;
    end
    else if StarP >= 0 then
    begin
      StarN := StarN + 1;
      N := StarN;
      P := StarP + 1;
    end
    else
      Exit(False);
  end;
  { The name is used up: only trailing stars may remain. }
  while (P < PLen) and (OrdAt(APattern, P) = CH_STAR) do
    P := P + 1;
  Result := P = PLen;
end;

{ The entry names in ADir, sorted.  Empty for an empty or unreadable
  directory. }
function SortedEntries(const ADir: string): TList<string>;
var
  Listing: string;
  Parts: TList<string>;
  I: Int;
begin
  Result := TList<string>.Create();
  Listing := ListDir(ADir);
  if Listing = '' then
    Exit;
  Parts := SplitChar(Listing, CH_LF);
  for I := 0 to Parts.Count - 1 do
    if Parts[I] <> '' then
      Result.Add(Parts[I]);
  Result.Sort((A, B) -> CompareStr(A, B));
end;

procedure Walk(const ADir: string; AMatch: TPredicate<string>; AFound: TList<string>);
var
  Names: TList<string>;
  I: Int;
  Path: string;
  Kind: Int;
begin
  { ADir is '' only for the file-system root, so that paths come out as
    '/name' rather than '//name'. }
  if ADir = '' then
    Names := SortedEntries('/')
  else
    Names := SortedEntries(ADir);
  for I := 0 to Names.Count - 1 do
  begin
    Path := ADir + '/' + Names[I];
    Kind := _PathKind(Path, 0);
    { A link is classified by its target, but only a file target counts:
      a linked directory is not descended into. }
    if Kind = KIND_SYMLINK then
    begin
      if _PathKind(Path, 1) = KIND_FILE then
        Kind := KIND_FILE
      else
        Kind := 0;
    end;
    if Kind = KIND_DIR then
      Walk(Path, AMatch, AFound)
    else if (Kind = KIND_FILE) and AMatch(Path) then
      AFound.Add(Path);
  end;
end;

function FindFiles(const ARoot: string; AMatch: TPredicate<string>): TList<string>;
var
  Root: string;
begin
  Root := ARoot;
  { Strip trailing separators, but keep '/' itself. }
  while (Length(Root) > 1) and (OrdAt(Root, Length(Root) - 1) = Ord('/')) do
    Root := Copy(Root, 0, Length(Root) - 1);
  if (Root = '') or (_PathKind(Root, 1) <> KIND_DIR) then
    raise EDirectoryNotFound.Create('Directory not found: "' + ARoot + '"');
  Result := TList<string>.Create();
  if Root = '/' then
    Root := '';
  Walk(Root, AMatch, Result);
end;

function FindFiles(const ARoot, APattern: string): TList<string>;
begin
  Result := FindFiles(ARoot, P -> MatchGlob(ExtractFileName(P), APattern));
end;

end.
