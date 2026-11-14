{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for the file-system metadata and manipulation half of IO.Files:
  kinds, sizes, modification times, permissions, symbolic links, deleting,
  copying and moving files and trees, typed directory listings and the
  freedesktop.org trash.

  Every test works under its own scratch directory (FRoot), created in SetUp
  and removed in TearDown with rm -rf, so a failing DeleteTree cannot leave
  litter behind.  Outside (FOutside) is a sibling directory a symbolic link
  can point at, to prove recursive operations do not follow links out of
  the tree.

  The permission-denied tests are ignored when the suite runs as root,
  which ignores file modes.

  Self-registers via the initialization section. }

unit FileSystem.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, Generics.Collections, DateUtils, IO.Files;

type
  TFileSystemTests = class(TTestCase)
  private
    FRoot: string;
    FOutside: string;
    function P(const ARel: string): string;
    function BigContent: string;
    function RunningAsRoot: Boolean;
    function ExecBitsKept: Boolean;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { kinds }
    procedure TestKind_FileDirectoryMissing;
    procedure TestKind_SymlinkFollowedAndNot;
    procedure TestKind_DanglingSymlink;
    { size }
    procedure TestFileSize_Bytes;
    procedure TestFileSize_NotAFile;
    { modification time }
    procedure TestModified_SetAndGetMillis;
    procedure TestModified_Instant;
    procedure TestModified_Missing;
    procedure TestFileAge_IsUnixSeconds;
    { delete }
    procedure TestDeleteDirectory_Empty;
    procedure TestDeleteDirectory_NotEmptyRaises;
    procedure TestDeleteDirectory_MissingRaises;
    procedure TestDeleteTree_Nested;
    procedure TestDeleteTree_DoesNotFollowSymlinks;
    procedure TestDeleteTree_OnSymlinkRemovesOnlyTheLink;
    procedure TestDeleteTree_MissingRaises;
    procedure TestDeleteTree_PermissionDeniedRaises;
    { copy }
    procedure TestCopyFile_LargerThanOneBuffer;
    procedure TestCopyFile_EmptyFile;
    procedure TestCopyFile_ExistingTargetRefused;
    procedure TestCopyFile_ExistingTargetReplaced;
    procedure TestCopyFile_MissingSourceRaises;
    procedure TestCopyFile_KeepsModifiedOnRequest;
    procedure TestCopyFile_KeepsPermissions;
    procedure TestCopyFile_UnreadableSourceRaises;
    procedure TestCopyFile_Utf8Path;
    procedure TestCopyTree_Nested;
    procedure TestCopyTree_SymlinksCopiedAsLinks;
    procedure TestCopyTree_ExistingTargetRefused;
    procedure TestCopyTree_KeepsModified;
    { move }
    procedure TestMove_File;
    procedure TestMove_Directory;
    procedure TestMove_ExistingTargetRefused;
    procedure TestMove_ExistingTargetReplaced;
    procedure TestMove_MissingSourceRaises;
    procedure TestMove_CopyFallbackMovesTree;
    { listing }
    procedure TestListDirectory_TypesSizesTimes;
    procedure TestListDirectory_MissingRaises;
    procedure TestListDirectory_Utf8Names;
    { checks }
    procedure TestIsHidden;
    procedure TestPermissions_ReadableWritableExecutable;
    procedure TestPermissions_MissingRaises;
    { links }
    procedure TestSymlink_CreateAndRead;
    procedure TestSymlink_ExistingRaises;
    procedure TestReadSymlink_NotALinkRaises;
    { trash }
    procedure TestTrashTo_FreedesktopLayout;
    procedure TestTrashTo_NameClash;
    procedure TestTrashTo_MissingSource;
    { errors }
    procedure TestError_CarriesPathAndCode;
  end;

implementation

const
  BIG_SIZE = 300007;       { several copy buffers, not a multiple of one }
  MODE_755 = $1ED;
  MODE_644 = $1A4;
  MODE_600 = $180;
  MODE_444 = $124;
  MODE_000 = 0;
  { 2020-09-13T12:26:40.123Z: a millisecond part a seconds-only clock loses. }
  STAMP_MS = 1600000000123;

{ Make APath and everything below it owner-accessible again (a test may
  have taken the permissions away), then remove it all, if it is there. }
procedure RemoveTree(const APath: string);

  procedure Unlock(const APath: string);
  var
    Names: TList<TDirEntry>;
    I: Int;
  begin
    SetPermissions(APath, $1C0);
    Names := ListDirectory(APath);
    for I := 0 to Names.Count - 1 do
      if Names[I].Kind = fkDirectory then
        Unlock(APath + '/' + Names[I].Name)
      else if Names[I].Kind = fkFile then
        SetPermissions(APath + '/' + Names[I].Name, $180);
  end;

begin
  if GetFileKind(APath, False) = fkNone then
    Exit;
  if GetFileKind(APath, False) = fkDirectory then
    Unlock(APath);
  DeleteTree(APath);
end;

function TFileSystemTests.P(const ARel: string): string;
begin
  Result := FRoot + '/' + ARel;
end;

function TFileSystemTests.BigContent: string;
var
  I: Int;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  for I := 0 to BIG_SIZE - 1 do
    SB.Append(Chr(I mod 251));
  Result := SB.ToString();
end;

function TFileSystemTests.RunningAsRoot: Boolean;
begin
  { root ignores file modes: a 000 file is still readable. }
  WriteFile(P('rootprobe'), 'x');
  SetPermissions(P('rootprobe'), MODE_000);
  Result := IsReadable(P('rootprobe'));
  SetPermissions(P('rootprobe'), MODE_644);
  DeleteFile(P('rootprobe'));
end;

{ Whether the file system keeps a file's execute bits as set.  Windows
  decides a program by its extension, not a mode. }
function TFileSystemTests.ExecBitsKept: Boolean;
begin
  WriteFile(P('modeprobe'), 'x');
  SetPermissions(P('modeprobe'), MODE_755);
  Result := GetPermissions(P('modeprobe')) = MODE_755;
  SetPermissions(P('modeprobe'), MODE_644);
  DeleteFile(P('modeprobe'));
end;

procedure TFileSystemTests.SetUp;
var
  Base: string;
begin
  Base := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-fs-' +
    IntToStr(GetProcessID());
  RemoveTree(Base);
  FRoot := Base + '/root';
  FOutside := Base + '/outside';
  ForceDirectories(FRoot);
  ForceDirectories(FOutside);
  WriteFile(FOutside + '/keep.txt', 'keep');
end;

procedure TFileSystemTests.TearDown;
var
  Base: string;
begin
  Base := ExtractFileDir(FRoot);
  RemoveTree(Base);
end;

{ ---- kinds ----------------------------------------------------------------- }

procedure TFileSystemTests.TestKind_FileDirectoryMissing;
begin
  WriteFile(P('f'), 'x');
  ForceDirectories(P('d'));
  AssertTrue('file', GetFileKind(P('f')) = fkFile);
  AssertTrue('directory', GetFileKind(P('d')) = fkDirectory);
  AssertTrue('missing', GetFileKind(P('nope')) = fkNone);
  AssertTrue('missing, not following', GetFileKind(P('nope'), False) = fkNone);
end;

procedure TFileSystemTests.TestKind_SymlinkFollowedAndNot;
begin
  ForceDirectories(P('d'));
  CreateSymlink(P('d'), P('ld'));
  AssertTrue('followed: the target', GetFileKind(P('ld')) = fkDirectory);
  AssertTrue('not followed: the link', GetFileKind(P('ld'), False) = fkSymlink);
end;

procedure TFileSystemTests.TestKind_DanglingSymlink;
begin
  CreateSymlink(P('gone'), P('dangling'));
  AssertTrue('followed: nothing there', GetFileKind(P('dangling')) = fkNone);
  AssertTrue('not followed: the link', GetFileKind(P('dangling'), False) = fkSymlink);
end;

{ ---- size ------------------------------------------------------------------ }

procedure TFileSystemTests.TestFileSize_Bytes;
begin
  WriteFile(P('big'), BigContent());
  WriteFile(P('empty'), '');
  AssertEquals('big', Int64(BIG_SIZE), FileSize(P('big')));
  AssertEquals('empty', Int64(0), FileSize(P('empty')));
  CreateSymlink(P('big'), P('lbig'));
  AssertEquals('through a link', Int64(BIG_SIZE), FileSize(P('lbig')));
end;

procedure TFileSystemTests.TestFileSize_NotAFile;
begin
  ForceDirectories(P('d'));
  AssertEquals('missing', Int64(-1), FileSize(P('nope')));
  AssertEquals('directory', Int64(-1), FileSize(P('d')));
end;

{ ---- modification time ----------------------------------------------------- }

procedure TFileSystemTests.TestModified_SetAndGetMillis;
begin
  WriteFile(P('f'), 'x');
  SetModifiedMillis(P('f'), STAMP_MS);
  AssertEquals('millisecond precision', STAMP_MS, GetModifiedMillis(P('f')));
  ForceDirectories(P('d'));
  SetModifiedMillis(P('d'), STAMP_MS);
  AssertEquals('a directory too', STAMP_MS, GetModifiedMillis(P('d')));
end;

procedure TFileSystemTests.TestModified_Instant;
var
  T: TInstant;
begin
  WriteFile(P('f'), 'x');
  SetModified(P('f'), MakeInstantUnixMillis(STAMP_MS));
  T := GetModified(P('f'));
  AssertEquals('instant', STAMP_MS, T.ToUnixMillis());
end;

procedure TFileSystemTests.TestModified_Missing;
var
  Raised: Boolean;
begin
  AssertEquals('missing reads -1', Int64(-1), GetModifiedMillis(P('nope')));
  Raised := False;
  try
    SetModifiedMillis(P('nope'), STAMP_MS);
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('setting a missing file raises', Raised);
end;

procedure TFileSystemTests.TestFileAge_IsUnixSeconds;
begin
  { FileAge (SysUtils) is the modification time in whole Unix seconds. }
  WriteFile(P('f'), 'x');
  SetModifiedMillis(P('f'), STAMP_MS);
  AssertEquals('seconds', STAMP_MS div 1000, FileAge(P('f')));
  AssertEquals('missing', Int64(-1), FileAge(P('nope')));
end;

{ ---- delete ---------------------------------------------------------------- }

procedure TFileSystemTests.TestDeleteDirectory_Empty;
begin
  ForceDirectories(P('d'));
  DeleteDirectory(P('d'));
  AssertTrue('gone', GetFileKind(P('d')) = fkNone);
end;

procedure TFileSystemTests.TestDeleteDirectory_NotEmptyRaises;
var
  Raised: Boolean;
begin
  ForceDirectories(P('d'));
  WriteFile(P('d/f'), 'x');
  Raised := False;
  try
    DeleteDirectory(P('d'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertTrue('still there', FileExists(P('d/f')));
end;

procedure TFileSystemTests.TestDeleteDirectory_MissingRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    DeleteDirectory(P('nope'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestDeleteTree_Nested;
begin
  ForceDirectories(P('t/a/b/c'));
  WriteFile(P('t/top'), '1');
  WriteFile(P('t/a/b/c/leaf'), '2');
  WriteFile(P('t/a/.hidden'), '3');
  DeleteTree(P('t'));
  AssertTrue('gone', GetFileKind(P('t'), False) = fkNone);
end;

procedure TFileSystemTests.TestDeleteTree_DoesNotFollowSymlinks;
begin
  ForceDirectories(P('t'));
  CreateSymlink(FOutside, P('t/out'));
  CreateSymlink(FOutside + '/keep.txt', P('t/outfile'));
  DeleteTree(P('t'));
  AssertTrue('tree gone', GetFileKind(P('t'), False) = fkNone);
  AssertTrue('outside directory untouched', FileExists(FOutside + '/keep.txt'));
end;

procedure TFileSystemTests.TestDeleteTree_OnSymlinkRemovesOnlyTheLink;
begin
  CreateSymlink(FOutside, P('link'));
  DeleteTree(P('link'));
  AssertTrue('link gone', GetFileKind(P('link'), False) = fkNone);
  AssertTrue('target untouched', FileExists(FOutside + '/keep.txt'));
end;

procedure TFileSystemTests.TestDeleteTree_MissingRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    DeleteTree(P('nope'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestDeleteTree_PermissionDeniedRaises;
var
  Raised: Boolean;
begin
  if RunningAsRoot() then begin Ignore('root ignores file modes'); Exit; end;
  ForceDirectories(P('t/locked'));
  WriteFile(P('t/locked/f'), 'x');
  SetPermissions(P('t/locked'), $16D);   { r-xr-xr-x: entries cannot be removed }
  Raised := False;
  try
    DeleteTree(P('t'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  SetPermissions(P('t/locked'), MODE_755);
  AssertTrue('failure reported, not ignored', Raised);
  AssertTrue('the undeletable file is still there', FileExists(P('t/locked/f')));
end;

{ ---- copy ------------------------------------------------------------------ }

procedure TFileSystemTests.TestCopyFile_LargerThanOneBuffer;
var
  Big: string;
begin
  Big := BigContent();
  WriteFile(P('src'), Big);
  CopyFile(P('src'), P('dst'));
  AssertEquals('size', Int64(BIG_SIZE), FileSize(P('dst')));
  AssertTrue('identical bytes', ReadFile(P('dst')) = Big);
end;

procedure TFileSystemTests.TestCopyFile_EmptyFile;
begin
  WriteFile(P('src'), '');
  CopyFile(P('src'), P('dst'));
  AssertTrue('exists', GetFileKind(P('dst')) = fkFile);
  AssertEquals('empty', Int64(0), FileSize(P('dst')));
end;

procedure TFileSystemTests.TestCopyFile_ExistingTargetRefused;
var
  Raised: Boolean;
begin
  WriteFile(P('src'), 'new');
  WriteFile(P('dst'), 'old');
  Raised := False;
  try
    CopyFile(P('src'), P('dst'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertEquals('target untouched', 'old', ReadFile(P('dst')));
end;

procedure TFileSystemTests.TestCopyFile_ExistingTargetReplaced;
begin
  WriteFile(P('src'), 'new');
  WriteFile(P('dst'), 'old and longer');
  CopyFile(P('src'), P('dst'), True);
  AssertEquals('replaced', 'new', ReadFile(P('dst')));
end;

procedure TFileSystemTests.TestCopyFile_MissingSourceRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    CopyFile(P('nope'), P('dst'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertTrue('no target created', GetFileKind(P('dst')) = fkNone);
end;

procedure TFileSystemTests.TestCopyFile_KeepsModifiedOnRequest;
begin
  WriteFile(P('src'), 'x');
  SetModifiedMillis(P('src'), STAMP_MS);
  CopyFile(P('src'), P('kept'), False, True);
  CopyFile(P('src'), P('fresh'));
  AssertEquals('kept', STAMP_MS, GetModifiedMillis(P('kept')));
  AssertTrue('not kept by default', GetModifiedMillis(P('fresh')) <> STAMP_MS);
end;

procedure TFileSystemTests.TestCopyFile_KeepsPermissions;
begin
  WriteFile(P('ro'), 'x');
  SetPermissions(P('ro'), MODE_444);
  CopyFile(P('ro'), P('ro2'));
  AssertEquals('read-only mode', MODE_444, GetPermissions(P('ro2')));
  { root may write a read-only file, so access() reports it writable }
  if not RunningAsRoot() then
    AssertTrue('read-only', not IsWritable(P('ro2')));
  if not ExecBitsKept() then
    Exit;
  WriteFile(P('tool'), '#!/bin/sh');
  SetPermissions(P('tool'), MODE_755);
  CopyFile(P('tool'), P('tool2'));
  AssertEquals('mode', MODE_755, GetPermissions(P('tool2')));
  AssertTrue('executable', IsExecutable(P('tool2')));
end;

procedure TFileSystemTests.TestCopyFile_UnreadableSourceRaises;
var
  Raised: Boolean;
begin
  if RunningAsRoot() then begin Ignore('root ignores file modes'); Exit; end;
  WriteFile(P('secret'), 'x');
  SetPermissions(P('secret'), MODE_000);
  Raised := False;
  try
    CopyFile(P('secret'), P('dst'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('permission denied raised', Raised);
end;

procedure TFileSystemTests.TestCopyFile_Utf8Path;
var
  Dir: string;
begin
  { Swedish, Greek and Japanese in one name, spelt as UTF-8 bytes. }
  Dir := P('v'#$C3#$A4'rld-'#$CE#$BA#$CF#$8C#$CF#$83#$CE#$BC#$CE#$BF#$CF#$82'-'#$E4#$B8#$96#$E7#$95#$8C);
  ForceDirectories(Dir);
  WriteFile(Dir + '/l'#$C3#$A5'da.dat', 'utf8');
  CopyFile(Dir + '/l'#$C3#$A5'da.dat', Dir + '/kopia-'#$C3#$B6'.dat');
  AssertEquals('copied', 'utf8', ReadFile(Dir + '/kopia-'#$C3#$B6'.dat'));
  AssertEquals('size', Int64(4), FileSize(Dir + '/kopia-'#$C3#$B6'.dat'));
  MovePath(Dir, P('moved-'#$C3#$A4));
  AssertTrue('moved', FileExists(P('moved-'#$C3#$A4'/l'#$C3#$A5'da.dat')));
  DeleteTree(P('moved-'#$C3#$A4));
  AssertTrue('deleted', GetFileKind(P('moved-'#$C3#$A4)) = fkNone);
end;

procedure TFileSystemTests.TestCopyTree_Nested;
var
  Big: string;
begin
  Big := BigContent();
  ForceDirectories(P('src/a/b'));
  ForceDirectories(P('src/empty'));
  WriteFile(P('src/top'), 'top');
  WriteFile(P('src/a/b/big'), Big);
  CopyTree(P('src'), P('dst'));
  AssertEquals('top', 'top', ReadFile(P('dst/top')));
  AssertTrue('big', ReadFile(P('dst/a/b/big')) = Big);
  AssertTrue('empty directory copied', GetFileKind(P('dst/empty')) = fkDirectory);
  AssertTrue('source kept', FileExists(P('src/top')));
end;

procedure TFileSystemTests.TestCopyTree_SymlinksCopiedAsLinks;
begin
  ForceDirectories(P('src'));
  CreateSymlink(FOutside, P('src/out'));
  CreateSymlink('top', P('src/rel'));
  WriteFile(P('src/top'), 'top');
  CopyTree(P('src'), P('dst'));
  AssertTrue('directory link stays a link', GetFileKind(P('dst/out'), False) = fkSymlink);
  { A Windows link stores its target with one kind of separator. }
  AssertEquals('same target', ReplaceAll(FOutside, '\', '/'),
    ReplaceAll(ReadSymlink(P('dst/out')), '\', '/'));
  AssertEquals('relative target kept as written', 'top', ReadSymlink(P('dst/rel')));
  AssertEquals('relative link resolves inside the copy', 'top', ReadFile(P('dst/rel')));
  AssertTrue('outside not copied into the tree',
    GetFileKind(P('dst/out/keep.txt'), False) = fkFile);   { only via the link }
  DeleteTree(P('dst'));
  AssertTrue('outside survives deleting the copy', FileExists(FOutside + '/keep.txt'));
end;

procedure TFileSystemTests.TestCopyTree_ExistingTargetRefused;
var
  Raised: Boolean;
begin
  ForceDirectories(P('src'));
  ForceDirectories(P('dst'));
  Raised := False;
  try
    CopyTree(P('src'), P('dst'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestCopyTree_KeepsModified;
begin
  ForceDirectories(P('src/d'));
  WriteFile(P('src/d/f'), 'x');
  SetModifiedMillis(P('src/d/f'), STAMP_MS);
  CopyTree(P('src'), P('dst'), True);
  AssertEquals('file time kept', STAMP_MS, GetModifiedMillis(P('dst/d/f')));
end;

{ ---- move ------------------------------------------------------------------ }

procedure TFileSystemTests.TestMove_File;
begin
  WriteFile(P('a'), 'x');
  MovePath(P('a'), P('b'));
  AssertTrue('source gone', GetFileKind(P('a')) = fkNone);
  AssertEquals('target', 'x', ReadFile(P('b')));
end;

procedure TFileSystemTests.TestMove_Directory;
begin
  ForceDirectories(P('d/sub'));
  WriteFile(P('d/sub/f'), 'x');
  MovePath(P('d'), P('e'));
  AssertTrue('source gone', GetFileKind(P('d')) = fkNone);
  AssertEquals('content moved', 'x', ReadFile(P('e/sub/f')));
end;

procedure TFileSystemTests.TestMove_ExistingTargetRefused;
var
  Raised: Boolean;
begin
  WriteFile(P('a'), 'new');
  WriteFile(P('b'), 'old');
  Raised := False;
  try
    MovePath(P('a'), P('b'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
  AssertEquals('target untouched', 'old', ReadFile(P('b')));
  AssertEquals('source untouched', 'new', ReadFile(P('a')));
end;

procedure TFileSystemTests.TestMove_ExistingTargetReplaced;
begin
  WriteFile(P('a'), 'new');
  WriteFile(P('b'), 'old');
  MovePath(P('a'), P('b'), True);
  AssertEquals('replaced', 'new', ReadFile(P('b')));
  AssertTrue('source gone', GetFileKind(P('a')) = fkNone);
  { A directory target is replaced as a whole. }
  ForceDirectories(P('d1'));
  WriteFile(P('d1/one'), '1');
  ForceDirectories(P('d2'));
  WriteFile(P('d2/two'), '2');
  MovePath(P('d1'), P('d2'), True);
  AssertTrue('new content', FileExists(P('d2/one')));
  AssertTrue('old content gone', not FileExists(P('d2/two')));
end;

procedure TFileSystemTests.TestMove_MissingSourceRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    MovePath(P('nope'), P('b'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestMove_CopyFallbackMovesTree;
begin
  { The path MovePath takes when rename reports a cross-device move: copy
    the tree, keeping times, then delete the source.  Forced here, since a
    second device is not available to every test run. }
  ForceDirectories(P('d/sub'));
  WriteFile(P('d/sub/f'), 'x');
  SetModifiedMillis(P('d/sub/f'), STAMP_MS);
  CreateSymlink(FOutside, P('d/out'));
  MoveByCopy(P('d'), P('e'));
  AssertTrue('source gone', GetFileKind(P('d'), False) = fkNone);
  AssertEquals('content', 'x', ReadFile(P('e/sub/f')));
  AssertEquals('time kept', STAMP_MS, GetModifiedMillis(P('e/sub/f')));
  AssertTrue('link kept as a link', GetFileKind(P('e/out'), False) = fkSymlink);
  AssertTrue('outside untouched', FileExists(FOutside + '/keep.txt'));
end;

{ ---- listing --------------------------------------------------------------- }

procedure TFileSystemTests.TestListDirectory_TypesSizesTimes;
var
  L: TList<TDirEntry>;
begin
  WriteFile(P('b.log'), '12345');
  SetModifiedMillis(P('b.log'), STAMP_MS);
  ForceDirectories(P('a-dir'));
  CreateSymlink(FOutside, P('c-link'));
  WriteFile(P('.hidden'), '');
  L := ListDirectory(FRoot);
  AssertEquals('count', 4, Int32(L.Count));
  { byte order: '.' < 'a' < 'b' < 'c' }
  AssertEquals('0 name', '.hidden', L[0].Name);
  AssertEquals('1 name', 'a-dir', L[1].Name);
  AssertTrue('1 kind', L[1].Kind = fkDirectory);
  AssertEquals('2 name', 'b.log', L[2].Name);
  AssertTrue('2 kind', L[2].Kind = fkFile);
  AssertEquals('2 size', Int64(5), L[2].Size);
  AssertEquals('2 time', STAMP_MS, L[2].ModifiedMillis);
  AssertEquals('3 name', 'c-link', L[3].Name);
  AssertTrue('3 kind: the link itself', L[3].Kind = fkSymlink);
end;

procedure TFileSystemTests.TestListDirectory_MissingRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    ListDirectory(P('nope'));
  except
    on E: EDirectoryNotFound do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestListDirectory_Utf8Names;
var
  L: TList<TDirEntry>;
begin
  WriteFile(P('sk'#$C3#$A4'rmbild.png'), 'png');
  L := ListDirectory(FRoot);
  AssertEquals('count', 1, Int32(L.Count));
  AssertEquals('name', 'sk'#$C3#$A4'rmbild.png', L[0].Name);
  AssertEquals('size', Int64(3), L[0].Size);
end;

{ ---- checks ---------------------------------------------------------------- }

procedure TFileSystemTests.TestIsHidden;
begin
  AssertTrue('dot name', IsHidden(P('.minecraft')));
  AssertTrue('plain name', not IsHidden(P('saves')));
  AssertTrue('only the last name counts', not IsHidden(P('.config/x')));
  AssertTrue('trailing slash', IsHidden(P('.config/')));
  AssertTrue('. is not hidden', not IsHidden('.'));
  AssertTrue('.. is not hidden', not IsHidden('..'));
end;

procedure TFileSystemTests.TestPermissions_ReadableWritableExecutable;
begin
  WriteFile(P('f'), 'x');
  SetPermissions(P('f'), MODE_644);
  AssertEquals('mode', MODE_644, GetPermissions(P('f')));
  AssertTrue('readable', IsReadable(P('f')));
  AssertTrue('writable', IsWritable(P('f')));
  AssertTrue('not executable', not IsExecutable(P('f')));
  if ExecBitsKept() then
  begin
    SetPermissions(P('f'), MODE_755);
    AssertTrue('executable', IsExecutable(P('f')));
  end;
  AssertTrue('missing is not readable', not IsReadable(P('nope')));
  AssertEquals('missing mode', -1, GetPermissions(P('nope')));
  if not RunningAsRoot() then
  begin
    SetPermissions(P('f'), MODE_000);
    AssertTrue('unreadable', not IsReadable(P('f')));
    AssertTrue('unwritable', not IsWritable(P('f')));
    SetPermissions(P('f'), MODE_600);
  end;
end;

procedure TFileSystemTests.TestPermissions_MissingRaises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    SetPermissions(P('nope'), MODE_644);
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

{ ---- links ----------------------------------------------------------------- }

procedure TFileSystemTests.TestSymlink_CreateAndRead;
begin
  WriteFile(P('f'), 'through');
  CreateSymlink('f', P('l'));
  AssertEquals('target as written', 'f', ReadSymlink(P('l')));
  AssertEquals('reads through', 'through', ReadFile(P('l')));
end;

procedure TFileSystemTests.TestSymlink_ExistingRaises;
var
  Raised: Boolean;
begin
  WriteFile(P('l'), 'x');
  Raised := False;
  try
    CreateSymlink('f', P('l'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

procedure TFileSystemTests.TestReadSymlink_NotALinkRaises;
var
  Raised: Boolean;
begin
  WriteFile(P('f'), 'x');
  Raised := False;
  try
    ReadSymlink(P('f'));
  except
    on E: EFileSystemError do
      Raised := True;
  end;
  AssertTrue('raised', Raised);
end;

{ ---- trash ----------------------------------------------------------------- }

{ APath as the trashinfo Path= key writes it, for the characters a temporary
  directory's path can hold. }
function Escaped(const APath: string): string;
begin
  Result := ReplaceAll(ReplaceAll(ReplaceAll(APath, ' ', '%20'), ':', '%3A'),
    '\', '%5C');
end;

procedure TFileSystemTests.TestTrashTo_FreedesktopLayout;
var
  Info: string;
begin
  WriteFile(P('old world.dat'), 'x');
  AssertTrue('trashed', TrashTo(P('old world.dat'), P('Trash')));
  AssertTrue('source gone', GetFileKind(P('old world.dat')) = fkNone);
  AssertEquals('in files/', 'x', ReadFile(P('Trash/files/old world.dat')));
  Info := ReadFile(P('Trash/info/old world.dat.trashinfo'));
  AssertTrue('header', Pos('[Trash Info]', Info) = 0);
  AssertTrue('original path, percent-encoded',
    Pos('Path=' + Escaped(FRoot) + '/old%20world.dat', Info) > 0);
  AssertTrue('deletion date', Pos('DeletionDate=', Info) > 0);
end;

procedure TFileSystemTests.TestTrashTo_NameClash;
begin
  ForceDirectories(P('a'));
  ForceDirectories(P('b'));
  WriteFile(P('a/log'), '1');
  WriteFile(P('b/log'), '2');
  AssertTrue('first', TrashTo(P('a/log'), P('Trash')));
  AssertTrue('second', TrashTo(P('b/log'), P('Trash')));
  AssertEquals('first kept', '1', ReadFile(P('Trash/files/log')));
  AssertTrue('second under a new name', GetFileKind(P('Trash/files/log.2')) = fkFile);
  AssertTrue('its info', GetFileKind(P('Trash/info/log.2.trashinfo')) = fkFile);
end;

procedure TFileSystemTests.TestTrashTo_MissingSource;
begin
  AssertTrue('nothing to trash', not TrashTo(P('nope'), P('Trash')));
end;

{ ---- errors ---------------------------------------------------------------- }

procedure TFileSystemTests.TestError_CarriesPathAndCode;
var
  Path: string;
  Code: Int;
begin
  Path := '';
  Code := 0;
  try
    DeleteDirectory(P('nope'));
  except
    on E: EFileSystemError do
    begin
      Path := E.Path;
      Code := E.OsError;
    end;
  end;
  AssertEquals('path', P('nope'), Path);
  AssertEquals('ENOENT', 2, Code);
end;

initialization
  RegisterTest(TFileSystemTests);

end.
