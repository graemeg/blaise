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
  TList<string>, and Generics.Collections already uses SysUtils.

  The second half of the unit is file-system metadata and manipulation, the
  ground java.nio.file.Files covers: what a path is (GetFileKind), its size,
  modification time and permissions, symbolic links, deleting, copying and
  moving files and whole trees, typed directory listings and the trash.

    * Queries answer with a sentinel (fkNone, -1, False) for a path that is
      not there.  Operations that change the file system raise
      EFileSystemError when they fail, carrying the path and the OS error
      code, and never fail silently.
    * Recursive operations (DeleteTree, CopyTree, MoveByCopy) never follow a
      symbolic link out of the tree: a link inside it is deleted, copied or
      moved as a link.
    * Paths are byte strings, so UTF-8 names work unchanged.
    * POSIX only (Linux, macOS, FreeBSD), like the rest of the RTL.  Blaise
      has no Windows target, so the Windows notes in the requests behind
      this unit (the hidden attribute, the recycle bin) do not apply yet.

  Streaming reads and writes of large files (hashing, unzipping) belong to
  the Streams unit: TFileInputStream and TFileOutputStream read and write
  through a file descriptor in caller-sized chunks, with Int64 Seek and
  Size, and never load the whole file.  CopyFile below streams the same
  way.

  FileAge (SysUtils, a compiler built-in) is the modification time of a
  path, following symbolic links, in WHOLE Unix seconds -- not a TDateTime
  or a DOS date as in Delphi -- and -1 when the path does not exist.  It is
  the same on every POSIX target.  GetModifiedMillis is the millisecond
  version, GetModified the full-precision TInstant. }

unit IO.Files;

interface

uses
  SysUtils,
  Generics.Collections,
  Functional,
  DateUtils;

type
  { Raised by FindFiles when its root is not an existing directory. }
  EDirectoryNotFound = class(EInOutError)
  end;

  { What a path names.  fkOther covers FIFOs, sockets and devices. }
  TFileKind = (fkNone, fkFile, fkDirectory, fkSymlink, fkOther);

  { Raised when a file-system operation fails.  OsError is the errno value
    (2 ENOENT, 13 EACCES, 17 EEXIST, 18 EXDEV, ...); Path is the path the
    failing call was given. }
  EFileSystemError = class(EInOutError)
  private
    FPath: string;
    FOsError: Int;
  public
    constructor Create(const AOperation, APath: string; AOsError: Int);
    property Path: string read FPath;
    property OsError: Int read FOsError;
  end;

  { One entry of a ListDirectory result.  Kind, Size, ModifiedMillis and
    Permissions describe the entry ITSELF: a symbolic link reports fkSymlink
    and the link's own size and time (call GetFileKind(Path, True) for what
    it points at).  Size is the byte count of a file and the file system's
    figure for anything else. }
  TDirEntry = record
    Name: string;
    Kind: TFileKind;
    Size: Int64;
    ModifiedMillis: Int64;
    Permissions: Int32;
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

{ ---- metadata --------------------------------------------------------------- }

{ What APath names.  AFollowLinks = True (the default) describes the target
  of a symbolic link, and fkNone for a dangling link; False describes the
  link itself (fkSymlink). }
function GetFileKind(const APath: string; AFollowLinks: Boolean = True): TFileKind;

{ The size in bytes of the regular file APath (following links), from its
  metadata, without reading it.  -1 when APath is missing or not a regular
  file. }
function FileSize(const APath: string): Int64;

{ The modification time of APath (following links) in milliseconds since
  the Unix epoch, or -1 when it is missing. }
function GetModifiedMillis(const APath: string): Int64;

{ The modification time of APath (following links) at full precision.
  Raises EFileSystemError when it is missing. }
function GetModified(const APath: string): TInstant;

{ Set the modification time of the file or directory APath (following
  links), leaving its access time alone.  Raises EFileSystemError. }
procedure SetModifiedMillis(const APath: string; AMillis: Int64);
procedure SetModified(const APath: string; const AWhen: TInstant);

{ The permission bits of APath (following links): the 12 low bits of
  st_mode, e.g. $1ED = octal 755.  -1 when it is missing. }
function GetPermissions(const APath: string): Int32;

{ chmod: set the permission bits of APath (following links).  Raises
  EFileSystemError. }
procedure SetPermissions(const APath: string; AMode: Int32);

{ access(2) checks for the calling process.  False when APath is missing.
  IsExecutable is True for a searchable directory too. }
function IsReadable(const APath: string): Boolean;
function IsWritable(const APath: string): Boolean;
function IsExecutable(const APath: string): Boolean;

{ True when the last name in APath starts with '.' (and is not '.' or
  '..'), the Unix convention.  Looks at the name only; APath need not
  exist. }
function IsHidden(const APath: string): Boolean;

{ ---- symbolic links --------------------------------------------------------- }

{ Create a symbolic link at ALinkPath whose content is ATarget, stored as
  written (a relative ATarget is resolved against the link's directory when
  followed).  ATarget need not exist.  Raises EFileSystemError, for example
  when ALinkPath already exists. }
procedure CreateSymlink(const ATarget, ALinkPath: string);

{ The content of the symbolic link ALinkPath, as written.  Raises
  EFileSystemError when it is not a link. }
function ReadSymlink(const ALinkPath: string): string;

{ ---- delete ----------------------------------------------------------------- }

{ Remove the EMPTY directory APath.  Raises EFileSystemError when it is
  missing, not empty or not a directory. }
procedure DeleteDirectory(const APath: string);

{ Remove APath and, if it is a directory, everything below it.  A symbolic
  link anywhere in the tree, APath included, is removed as a link; what it
  points at is never touched.  Stops at the first entry that cannot be
  removed and raises EFileSystemError naming it (the entries already
  removed stay removed).  A missing APath raises too. }
procedure DeleteTree(const APath: string);

{ ---- copy and move ---------------------------------------------------------- }

{ Copy the regular file ASource (following links) to ATarget, streaming
  through a fixed buffer so a file of any size copies in constant memory.
  The copy gets ASource's permission bits.  ATarget must not exist unless
  AReplace; a replaced symbolic link is replaced, not written through.
  AKeepModified gives the copy ASource's modification time.  Raises
  EFileSystemError (a missing or unreadable source, an existing or
  unwritable target, a directory on either side); a half-written target is
  removed. }
procedure CopyFile(const ASource, ATarget: string; AReplace: Boolean = False;
  AKeepModified: Boolean = False);

{ Copy the directory tree ASource to ATarget, which must not exist.  Files
  are copied as CopyFile does, directories get their source's permission
  bits, and symbolic links are recreated as links with the same content
  (never followed, so a link out of the tree stays a link).  ASource itself
  is followed if it is a link.  AKeepModified keeps the modification time
  of every file and directory.  Raises EFileSystemError; a partial copy is
  left in place for the caller to inspect or DeleteTree. }
procedure CopyTree(const ASource, ATarget: string; AKeepModified: Boolean = False);

{ Move (rename) the file, directory or link ASource to ATarget.  When the
  rename fails because the two are on different devices (EXDEV), falls
  back to MoveByCopy.  ATarget must not exist unless AReplace; a replaced
  directory is replaced as a whole, and is only deleted once the move has
  succeeded.  Raises EFileSystemError. }
procedure MovePath(const ASource, ATarget: string; AReplace: Boolean = False);

{ The cross-device half of MovePath: copy ASource to ATarget (which must
  not exist) keeping modification times, links as links, then DeleteTree
  ASource.  If the copy fails, the partial target is removed and ASource
  is left as it was.  Raises EFileSystemError. }
procedure MoveByCopy(const ASource, ATarget: string);

{ ---- listing ---------------------------------------------------------------- }

{ The entries of the directory APath (following a link to it), sorted by
  name in byte order, each with its kind, size, time and permissions from
  one lstat.  '.' and '..' are not included.  Raises EDirectoryNotFound
  when APath is not a directory.  Caller owns the list. }
function ListDirectory(const APath: string): TList<TDirEntry>;

{ ---- trash ------------------------------------------------------------------ }

{ Move APath to the user's trash, where the desktop can restore it.  On
  Linux and FreeBSD that is the freedesktop.org home trash,
  $XDG_DATA_HOME/Trash (default ~/.local/share/Trash), through TrashTo.  On
  macOS it is ~/.Trash, by rename: Finder shows the item but cannot "Put
  Back", which needs NSFileManager's trashItemAtURL, out of reach of a
  plain-C stdlib (and on recent macOS a process without Full Disk Access
  may be refused).  Returns False, leaving APath alone, when there is no
  usable trash -- APath on another device than the trash, no home
  directory, permission refused -- so the caller can delete instead. }
function MoveToTrash(const APath: string): Boolean;

{ Move APath into the freedesktop.org trash directory ATrashDir (the
  Trash Specification 1.0): the item goes to ATrashDir/files/NAME and its
  original absolute path and deletion time to ATrashDir/info/NAME.trashinfo.
  NAME is APath's own name, or NAME.2, NAME.3, ... when that is taken.
  Returns False when APath is missing or the move fails (different
  device). }
function TrashTo(const APath, ATrashDir: string): Boolean;

implementation

uses
  StrUtils;

{ ---- OS bindings ------------------------------------------------------------ }

type
  { What _PathStat fills; see rtl.platform.posix. }
  TStatInfo = record
    Kind: Int32;
    Mode: Int32;
    Size: Int64;
    MtimeSec: Int64;
    MtimeNsec: Int64;
  end;

  TTimeSpec = record
    Sec: Int64;
    Nsec: Int64;
  end;

function _PathStat(const Path: string; FollowLinks: Int32; AOut: Pointer): Int64;
  external name '_PathStat';
{ The errno behind a failed call's result, in both link profiles
  (runtime.errno.*). }
function OsErrorOf(N: Int64): Int; external name 'OsErrorOf';
{ UTIME_OMIT for this target (rtl.platform.layout.*). }
function _UtimeOmit: Int64; external name '_UtimeOmit';
function _FdOpenWrite(Path: Pointer): Int32; external name '_FdOpenWrite';

function c_open(Path: PChar; Flags: Int32): Int32; external name 'open';
function c_close(Fd: Int32): Int32; external name 'close';
function c_read(Fd: Int32; Buf: Pointer; Count: Int64): Int64; external name 'read';
function c_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64; external name 'write';
function c_unlink(Path: PChar): Int32; external name 'unlink';
function c_rmdir(Path: PChar): Int32; external name 'rmdir';
function c_mkdir(Path: PChar; Mode: Int32): Int32; external name 'mkdir';
function c_rename(OldPath, NewPath: PChar): Int32; external name 'rename';
function c_chmod(Path: PChar; Mode: Int32): Int32; external name 'chmod';
function c_symlink(Target, LinkPath: PChar): Int32; external name 'symlink';
function c_readlink(Path: PChar; Buf: Pointer; Size: Int64): Int64; external name 'readlink';
function c_access(Path: PChar; Mode: Int32): Int32; external name 'access';
function c_futimens(Fd: Int32; Times: Pointer): Int32; external name 'futimens';

{ Imported from the RTL (rtl.platform.posix): 0 missing, 1 regular file,
  2 directory, 3 symbolic link, 4 other.  FollowLinks <> 0 stats the link's
  target; 0 reports the link itself. }
function _PathKind(const Path: string; FollowLinks: Int32): Int32; external name '_PathKind';

const
  KIND_FILE    = 1;
  KIND_DIR     = 2;
  KIND_SYMLINK = 3;

  O_RDONLY = 0;
  R_OK = 4;
  W_OK = 2;
  X_OK = 1;
  NANOS_PER_SEC = 1000000000;
  NANOS_PER_MS = 1000000;
  COPY_BUF_SIZE = 65536;
  MAX_LINK_LEN = 4096;
  MODE_DIR_WORKING = $1C0;      { rwx------ while a copied directory is filled }

  ENOENT = 2;
  EACCES = 13;
  EEXIST = 17;
  EXDEV = 18;
  ENOTDIR = 20;
  EISDIR = 21;

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

{ ===========================================================================
  Metadata and manipulation
  =========================================================================== }

function OsErrorText(ACode: Int): string;
begin
  case ACode of
    1: Result := 'operation not permitted';
    2: Result := 'no such file or directory';
    5: Result := 'input/output error';
    13: Result := 'permission denied';
    16: Result := 'resource busy';
    17: Result := 'file exists';
    18: Result := 'cross-device link';
    20: Result := 'not a directory';
    21: Result := 'is a directory';
    22: Result := 'invalid argument';
    28: Result := 'no space left on device';
    30: Result := 'read-only file system';
    36, 63: Result := 'file name too long';
    39, 66: Result := 'directory not empty';
    40, 62: Result := 'too many levels of symbolic links';
  else
    Result := 'error ' + IntToStr(ACode);
  end;
end;

constructor EFileSystemError.Create(const AOperation, APath: string; AOsError: Int);
begin
  inherited Create(AOperation + ' "' + APath + '": ' + OsErrorText(AOsError) +
    ' (errno ' + IntToStr(AOsError) + ')');
  FPath := APath;
  FOsError := AOsError;
end;

procedure Fail(const AOperation, APath: string; ACode: Int);
begin
  raise EFileSystemError.Create(AOperation, APath, ACode);
end;

{ Raise for a failed call result ARc (the errno is read before anything else
  can disturb it). }
procedure FailRc(const AOperation, APath: string; ARc: Int64);
var
  Code: Int;
begin
  Code := OsErrorOf(ARc);
  if Code = 0 then
    Code := 5;   { EIO: a failure that left no errno }
  raise EFileSystemError.Create(AOperation, APath, Code);
end;

function StatPath(const APath: string; AFollow: Boolean; out AInfo: TStatInfo): Int64;
var
  Follow: Int32;
begin
  Follow := 0;
  if AFollow then
    Follow := 1;
  Result := _PathStat(APath, Follow, @AInfo);
end;

function KindOf(ACode: Int32): TFileKind;
begin
  case ACode of
    KIND_FILE: Result := fkFile;
    KIND_DIR: Result := fkDirectory;
    KIND_SYMLINK: Result := fkSymlink;
    4: Result := fkOther;
  else
    Result := fkNone;
  end;
end;

function InfoMillis(const AInfo: TStatInfo): Int64;
begin
  Result := AInfo.MtimeSec * 1000 + AInfo.MtimeNsec div NANOS_PER_MS;
end;

function InfoNanos(const AInfo: TStatInfo): Int64;
begin
  Result := AInfo.MtimeSec * NANOS_PER_SEC + AInfo.MtimeNsec;
end;

function GetFileKind(const APath: string; AFollowLinks: Boolean = True): TFileKind;
var
  Info: TStatInfo;
begin
  if (APath = '') or (StatPath(APath, AFollowLinks, Info) <> 0) then
    Exit(fkNone);
  Result := KindOf(Info.Kind);
end;

function FileSize(const APath: string): Int64;
var
  Info: TStatInfo;
begin
  if (StatPath(APath, True, Info) <> 0) or (Info.Kind <> KIND_FILE) then
    Exit(-1);
  Result := Info.Size;
end;

function GetModifiedMillis(const APath: string): Int64;
var
  Info: TStatInfo;
begin
  if StatPath(APath, True, Info) <> 0 then
    Exit(-1);
  Result := InfoMillis(Info);
end;

function GetModified(const APath: string): TInstant;
var
  Info: TStatInfo;
  Rc: Int64;
begin
  Rc := StatPath(APath, True, Info);
  if Rc <> 0 then
    FailRc('Cannot read the modification time of', APath, Rc);
  Result.Nanoseconds := InfoNanos(Info);
end;

procedure SetModifiedNanos(const APath: string; ANanos: Int64);
var
  Fd: Int32;
  Rc: Int64;
  Times: array[0..1] of TTimeSpec;
begin
  { futimens on a read-only descriptor: setting times needs ownership, not
    write permission, and a directory opens read-only too. }
  Fd := c_open(PChar(APath), O_RDONLY);
  if Fd < 0 then
    FailRc('Cannot set the modification time of', APath, Fd);
  Times[0].Sec := 0;
  Times[0].Nsec := _UtimeOmit();
  Times[1].Sec := ANanos div NANOS_PER_SEC;
  Times[1].Nsec := ANanos mod NANOS_PER_SEC;
  if Times[1].Nsec < 0 then
  begin
    Times[1].Nsec := Times[1].Nsec + NANOS_PER_SEC;
    Times[1].Sec := Times[1].Sec - 1;
  end;
  Rc := c_futimens(Fd, @Times[0]);
  if Rc <> 0 then
  begin
    { Read the errno before close can replace it. }
    Rc := OsErrorOf(Rc);
    c_close(Fd);
    Fail('Cannot set the modification time of', APath, Int(Rc));
  end;
  c_close(Fd);
end;

procedure SetModifiedMillis(const APath: string; AMillis: Int64);
begin
  SetModifiedNanos(APath, AMillis * NANOS_PER_MS);
end;

procedure SetModified(const APath: string; const AWhen: TInstant);
begin
  SetModifiedNanos(APath, AWhen.Nanoseconds);
end;

function GetPermissions(const APath: string): Int32;
var
  Info: TStatInfo;
begin
  if StatPath(APath, True, Info) <> 0 then
    Exit(-1);
  Result := Info.Mode;
end;

procedure SetPermissions(const APath: string; AMode: Int32);
var
  Rc: Int64;
begin
  Rc := c_chmod(PChar(APath), AMode);
  if Rc <> 0 then
    FailRc('Cannot change the permissions of', APath, Rc);
end;

function IsReadable(const APath: string): Boolean;
begin
  Result := c_access(PChar(APath), R_OK) = 0;
end;

function IsWritable(const APath: string): Boolean;
begin
  Result := c_access(PChar(APath), W_OK) = 0;
end;

function IsExecutable(const APath: string): Boolean;
begin
  Result := c_access(PChar(APath), X_OK) = 0;
end;

{ The last name in APath, ignoring trailing separators. }
function LastName(const APath: string): string;
var
  S: string;
begin
  S := APath;
  while (Length(S) > 1) and (OrdAt(S, Length(S) - 1) = Ord('/')) do
    S := Copy(S, 0, Length(S) - 1);
  Result := ExtractFileName(S);
end;

function IsHidden(const APath: string): Boolean;
var
  Name: string;
begin
  Name := LastName(APath);
  Result := (Length(Name) > 0) and (OrdAt(Name, 0) = Ord('.')) and
    (Name <> '.') and (Name <> '..');
end;

{ ---- symbolic links --------------------------------------------------------- }

procedure CreateSymlink(const ATarget, ALinkPath: string);
var
  Rc: Int64;
begin
  Rc := c_symlink(PChar(ATarget), PChar(ALinkPath));
  if Rc <> 0 then
    FailRc('Cannot create the symbolic link', ALinkPath, Rc);
end;

function ReadSymlink(const ALinkPath: string): string;
var
  Buf: array of Byte;
  N: Int64;
  I: Int;
  SB: TStringBuilder;
begin
  SetLength(Buf, MAX_LINK_LEN);
  N := c_readlink(PChar(ALinkPath), @Buf[0], MAX_LINK_LEN);
  if N < 0 then
    FailRc('Cannot read the symbolic link', ALinkPath, N);
  SB := TStringBuilder.Create();
  for I := 0 to Int(N) - 1 do
    SB.AppendByte(Buf[I]);
  Result := SB.ToString();
end;

{ ---- delete ----------------------------------------------------------------- }

procedure DeleteDirectory(const APath: string);
var
  Rc: Int64;
begin
  Rc := c_rmdir(PChar(APath));
  if Rc <> 0 then
    FailRc('Cannot delete the directory', APath, Rc);
end;

procedure DeleteTree(const APath: string);
var
  Info: TStatInfo;
  Names: TList<string>;
  I: Int;
  Rc: Int64;
begin
  Rc := StatPath(APath, False, Info);
  if Rc <> 0 then
    FailRc('Cannot delete', APath, Rc);
  if Info.Kind <> KIND_DIR then
  begin
    { A file, or a link removed as a link (lstat above: never followed). }
    Rc := c_unlink(PChar(APath));
    if Rc <> 0 then
      FailRc('Cannot delete', APath, Rc);
    Exit;
  end;
  Names := SortedEntries(APath);
  for I := 0 to Names.Count - 1 do
    DeleteTree(APath + '/' + Names[I]);
  DeleteDirectory(APath);
end;

{ ---- copy ------------------------------------------------------------------- }

{ Write all ACount bytes at ABuf to AFd.  The result of the failing write,
  or 0. }
function WriteAll(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
var
  N: Int64;
begin
  while ACount > 0 do
  begin
    N := c_write(AFd, ABuf, ACount);
    if N < 0 then
      Exit(N);
    if N = 0 then
      Exit(-1);                   { no progress: a failure }
    ABuf := Pointer(PChar(ABuf) + N);
    ACount := ACount - N;
  end;
  Result := 0;
end;

procedure CopyFile(const ASource, ATarget: string; AReplace: Boolean = False;
  AKeepModified: Boolean = False);
var
  Src, Tgt: TStatInfo;
  InFd, OutFd: Int32;
  Buf: array of Byte;
  N, Rc: Int64;
  ReadErr, WriteErr: Int;
begin
  Rc := StatPath(ASource, True, Src);
  if Rc <> 0 then
    FailRc('Cannot copy', ASource, Rc);
  if Src.Kind = KIND_DIR then
    Fail('Cannot copy', ASource, EISDIR);
  InFd := c_open(PChar(ASource), O_RDONLY);
  if InFd < 0 then
    FailRc('Cannot open for copying', ASource, InFd);
  try
    if StatPath(ATarget, False, Tgt) = 0 then
    begin
      if not AReplace then
        Fail('Cannot copy to', ATarget, EEXIST);
      if Tgt.Kind = KIND_DIR then
        Fail('Cannot copy to', ATarget, EISDIR);
      { Replace the entry itself: a link is not written through. }
      Rc := c_unlink(PChar(ATarget));
      if Rc <> 0 then
        FailRc('Cannot replace', ATarget, Rc);
    end;
    OutFd := _FdOpenWrite(Pointer(ATarget));
    if OutFd < 0 then
      FailRc('Cannot create', ATarget, OutFd);
  except
    c_close(InFd);
    raise;
  end;
  SetLength(Buf, COPY_BUF_SIZE);
  ReadErr := 0;
  WriteErr := 0;
  while True do
  begin
    N := c_read(InFd, @Buf[0], COPY_BUF_SIZE);
    if N = 0 then
      Break;
    if N < 0 then
    begin
      ReadErr := OsErrorOf(N);
      Break;
    end;
    Rc := WriteAll(OutFd, @Buf[0], N);
    if Rc <> 0 then
    begin
      WriteErr := OsErrorOf(Rc);
      if WriteErr = 0 then
        WriteErr := 5;
      Break;
    end;
  end;
  c_close(InFd);
  { close reports a deferred write error (NFS, a full disk) }
  if (c_close(OutFd) <> 0) and (ReadErr = 0) and (WriteErr = 0) then
    WriteErr := 5;
  if (ReadErr <> 0) or (WriteErr <> 0) then
  begin
    c_unlink(PChar(ATarget));
    if ReadErr <> 0 then
      Fail('Cannot read', ASource, ReadErr)
    else
      Fail('Cannot write', ATarget, WriteErr);
  end;
  SetPermissions(ATarget, Src.Mode);
  if AKeepModified then
    SetModifiedNanos(ATarget, InfoNanos(Src));
end;

procedure MakeDir(const APath: string; AMode: Int32);
var
  Rc: Int64;
begin
  Rc := c_mkdir(PChar(APath), AMode);
  if Rc <> 0 then
    FailRc('Cannot create the directory', APath, Rc);
end;

{ Copy one entry -- file, link or directory tree -- to ATarget, which does not
  exist.  AFollow decides whether ASource itself is followed if it is a link;
  entries below it never are. }
procedure CopyEntry(const ASource, ATarget: string; AFollow, AKeepModified: Boolean);
var
  Info: TStatInfo;
  Names: TList<string>;
  I: Int;
  Rc: Int64;
begin
  Rc := StatPath(ASource, AFollow, Info);
  if Rc <> 0 then
    FailRc('Cannot copy', ASource, Rc);
  if Info.Kind = KIND_SYMLINK then
    CreateSymlink(ReadSymlink(ASource), ATarget)
  else if Info.Kind = KIND_DIR then
  begin
    { Owner-writable while it is filled, its own mode and time once done
      (adding the entries changes a directory's modification time). }
    MakeDir(ATarget, MODE_DIR_WORKING);
    Names := SortedEntries(ASource);
    for I := 0 to Names.Count - 1 do
      CopyEntry(ASource + '/' + Names[I], ATarget + '/' + Names[I], False,
        AKeepModified);
    SetPermissions(ATarget, Info.Mode);
    if AKeepModified then
      SetModifiedNanos(ATarget, InfoNanos(Info));
  end
  else if Info.Kind = KIND_FILE then
    CopyFile(ASource, ATarget, False, AKeepModified)
  else
    Fail('Cannot copy (not a file, directory or link)', ASource, 22);
end;

procedure CopyTree(const ASource, ATarget: string; AKeepModified: Boolean = False);
var
  Tgt: TStatInfo;
begin
  if StatPath(ATarget, False, Tgt) = 0 then
    Fail('Cannot copy to', ATarget, EEXIST);
  if GetFileKind(ASource, True) = fkNone then
    Fail('Cannot copy', ASource, ENOENT);
  if GetFileKind(ASource, True) <> fkDirectory then
    Fail('Cannot copy the tree', ASource, ENOTDIR);
  CopyEntry(ASource, ATarget, True, AKeepModified);
end;

{ ---- move ------------------------------------------------------------------- }

procedure MoveByCopy(const ASource, ATarget: string);
var
  Info: TStatInfo;
  Rc: Int64;
begin
  Rc := StatPath(ASource, False, Info);
  if Rc <> 0 then
    FailRc('Cannot move', ASource, Rc);
  if StatPath(ATarget, False, Info) = 0 then
    Fail('Cannot move to', ATarget, EEXIST);
  try
    CopyEntry(ASource, ATarget, False, True);
  except
    { Leave no half-moved target behind; the source is untouched. }
    if GetFileKind(ATarget, False) <> fkNone then
    try
      DeleteTree(ATarget);
    except
    end;
    raise;
  end;
  DeleteTree(ASource);
end;

procedure MovePath(const ASource, ATarget: string; AReplace: Boolean = False);
var
  Src, Tgt: TStatInfo;
  Rc: Int64;
  Code: Int;
  Aside: string;
begin
  Rc := StatPath(ASource, False, Src);
  if Rc <> 0 then
    FailRc('Cannot move', ASource, Rc);
  Aside := '';
  if StatPath(ATarget, False, Tgt) = 0 then
  begin
    if not AReplace then
      Fail('Cannot move to', ATarget, EEXIST);
    { rename replaces a file atomically; a directory target (or a directory
      onto a file) must first be moved out of the way, and is deleted only
      once the move has succeeded. }
    if (Tgt.Kind = KIND_DIR) or (Src.Kind = KIND_DIR) then
    begin
      Aside := ATarget + '.blaise-replaced-' + IntToStr(GetProcessID());
      Rc := c_rename(PChar(ATarget), PChar(Aside));
      if Rc <> 0 then
        FailRc('Cannot replace', ATarget, Rc);
    end;
    { A file onto a file: rename replaces it atomically. }
  end;
  Rc := c_rename(PChar(ASource), PChar(ATarget));
  if Rc <> 0 then
  begin
    Code := OsErrorOf(Rc);
    try
      if Code <> EXDEV then
        Fail('Cannot move ' + ASource + ' to', ATarget, Code);
      { Across devices.  A file target still present (AReplace, no Aside)
        goes now; MoveByCopy wants the name free. }
      if (Aside = '') and (GetFileKind(ATarget, False) <> fkNone) then
        DeleteTree(ATarget);
      MoveByCopy(ASource, ATarget);
    except
      if Aside <> '' then
        c_rename(PChar(Aside), PChar(ATarget));
      raise;
    end;
  end;
  if Aside <> '' then
    DeleteTree(Aside);
end;

{ ---- listing ---------------------------------------------------------------- }

function ListDirectory(const APath: string): TList<TDirEntry>;
var
  Names: TList<string>;
  I: Int;
  Info: TStatInfo;
  E: TDirEntry;
begin
  if _PathKind(APath, 1) <> KIND_DIR then
    raise EDirectoryNotFound.Create('Directory not found: "' + APath + '"');
  Result := TList<TDirEntry>.Create();
  Names := SortedEntries(APath);
  for I := 0 to Names.Count - 1 do
  begin
    { An entry removed since the directory was read is left out. }
    if StatPath(APath + '/' + Names[I], False, Info) <> 0 then
      Continue;
    E.Name := Names[I];
    E.Kind := KindOf(Info.Kind);
    E.Size := Info.Size;
    E.ModifiedMillis := InfoMillis(Info);
    E.Permissions := Info.Mode;
    Result.Add(E);
  end;
end;

{ ---- trash ------------------------------------------------------------------ }

const
  HEX_DIGITS = '0123456789ABCDEF';

{ RFC 2396 escaping for the trashinfo Path= key: unreserved bytes and '/'
  stay, everything else (space, '%', UTF-8 bytes, ...) becomes %XX. }
function EscapeTrashPath(const APath: string): string;
var
  I, B: Int;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  for I := 0 to Length(APath) - 1 do
  begin
    B := OrdAt(APath, I);
    if ((B >= Ord('A')) and (B <= Ord('Z'))) or ((B >= Ord('a')) and (B <= Ord('z'))) or
       ((B >= Ord('0')) and (B <= Ord('9'))) or (B = Ord('-')) or (B = Ord('_')) or
       (B = Ord('.')) or (B = Ord('~')) or (B = Ord('/')) then
      SB.Append(Chr(B))
    else
    begin
      SB.Append('%');
      SB.Append(Copy(HEX_DIGITS, B shr 4, 1));
      SB.Append(Copy(HEX_DIGITS, B and 15, 1));
    end;
  end;
  Result := SB.ToString();
end;

function Pad2(N: Int32): string;
begin
  Result := IntToStr(N);
  if N < 10 then
    Result := '0' + Result;
end;

{ Local time now as YYYY-MM-DDThh:mm:ss, the trashinfo DeletionDate form. }
function LocalStamp: string;
var
  Y, Mo, D, H, Mi, S, Ns: Int32;
begin
  _TimeSplit(_TimeNow() + Int64(_TimeLocalOffsetSecs()) * NANOS_PER_SEC,
    Y, Mo, D, H, Mi, S, Ns);
  Result := IntToStr(Y) + '-' + Pad2(Mo) + '-' + Pad2(D) + 'T' + Pad2(H) +
    ':' + Pad2(Mi) + ':' + Pad2(S);
end;

function AbsolutePath(const APath: string): string;
begin
  if (Length(APath) > 0) and (OrdAt(APath, 0) = Ord('/')) then
    Result := APath
  else
    Result := ExcludeTrailingPathDelimiter(GetCurrentDir()) + '/' + APath;
  while (Length(Result) > 1) and (OrdAt(Result, Length(Result) - 1) = Ord('/')) do
    Result := Copy(Result, 0, Length(Result) - 1);
end;

{ A name under AFilesDir (and, when AInfoDir <> '', AInfoDir with
  '.trashinfo') that is not taken yet: AName, then AName.2, AName.3, ... }
function FreeTrashName(const AFilesDir, AInfoDir, AName: string): string;
var
  N: Int;
begin
  Result := AName;
  N := 1;
  while (GetFileKind(AFilesDir + '/' + Result, False) <> fkNone) or
        ((AInfoDir <> '') and
         (GetFileKind(AInfoDir + '/' + Result + '.trashinfo', False) <> fkNone)) do
  begin
    N := N + 1;
    Result := AName + '.' + IntToStr(N);
  end;
end;

function TrashTo(const APath, ATrashDir: string): Boolean;
var
  Abs, Name, FilesDir, InfoDir, InfoPath: string;
begin
  Result := False;
  if GetFileKind(APath, False) = fkNone then
    Exit;
  Abs := AbsolutePath(APath);
  FilesDir := ATrashDir + '/files';
  InfoDir := ATrashDir + '/info';
  if not ForceDirectories(FilesDir) or not ForceDirectories(InfoDir) then
    Exit;
  Name := FreeTrashName(FilesDir, InfoDir, LastName(Abs));
  InfoPath := InfoDir + '/' + Name + '.trashinfo';
  { The spec's order: info first, so a crash never leaves an item in files/
    with no record of where it came from. }
  try
    WriteFile(InfoPath, '[Trash Info]' + #10 + 'Path=' + EscapeTrashPath(Abs) +
      #10 + 'DeletionDate=' + LocalStamp() + #10);
  except
    Exit;
  end;
  if c_rename(PChar(APath), PChar(FilesDir + '/' + Name)) <> 0 then
  begin
    c_unlink(PChar(InfoPath));
    Exit;
  end;
  Result := True;
end;

function MoveToTrash(const APath: string): Boolean;
var
  Home, Dir: string;
begin
  Result := False;
  Home := GetEnvironmentVariable('HOME');
  {$IFDEF DARWIN}
  if Home = '' then
    Exit;
  Dir := Home + '/.Trash';
  if (GetFileKind(APath, False) = fkNone) or (GetFileKind(Dir) <> fkDirectory) then
    Exit;
  Result := c_rename(PChar(APath),
    PChar(Dir + '/' + FreeTrashName(Dir, '', LastName(AbsolutePath(APath))))) = 0;
  {$ELSE}
  Dir := GetEnvironmentVariable('XDG_DATA_HOME');
  if Dir = '' then
  begin
    if Home = '' then
      Exit;
    Dir := Home + '/.local/share';
  end;
  Result := TrashTo(APath, Dir + '/Trash');
  {$ENDIF}
end;

end.
