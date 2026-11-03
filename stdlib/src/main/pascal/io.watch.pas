{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ IO.Watch: notification when files or directories change, for programs
  that must notice edits made by others (an IDE's open files, a build
  watching its sources).

    W := TFileWatcher.Create();
    W.Watch('src/main.pas');
    W.Watch('src');
    for C in W.Wait(500) do
      if C.Kind = fcDeleted then ... else ...;

  Behaviour:

    * Watch takes a file or a directory; False when it cannot be opened
      (missing, or no permission).  Watching is not recursive.
    * A file is Changed when its contents or attributes change; a
      directory is Changed when an entry is created, deleted or renamed.
    * Deleted means the watched path no longer names the object watched:
      it was deleted, or renamed away (the way editors save atomically:
      write a new file, rename it over the old).  The watch is dropped;
      Watch the path again if it reappears.
    * Wait blocks up to ATimeoutMs and returns each changed path once,
      Deleted taking precedence; an empty list on timeout.
    * One thread uses a watcher at a time.

  kqueue (EVFILT_VNODE) on macOS and FreeBSD, one descriptor per watched
  path; inotify on Linux.  The calls bind the bare POSIX names, which the
  static, libc-free profiles provide as syscall leaves, so a program using
  this unit is not forced to link libc. }

unit IO.Watch;

interface

uses
  SysUtils, Generics.Collections;

type
  TFileChangeKind = (fcChanged, fcDeleted);

  TFileChange = record
    Path: string;
    Kind: TFileChangeKind;
  end;

  TFileWatcher = class
  private
    FQueue: Int32;
    { kqueue: descriptor -> path.  inotify: watch descriptor -> path. }
    FPaths: TDictionary<Int64, string>;
    FIds: TDictionary<string, Int64>;
    FBuf: Pointer;
    procedure Drop(AId: Int64);
    procedure Note(AChanges: TList<TFileChange>; const APath: string; AKind: TFileChangeKind);
  public
    constructor Create();
    destructor Destroy(); override;
    function Watch(const APath: string): Boolean;
    procedure Unwatch(const APath: string);
    function Watching(const APath: string): Boolean;
    function Wait(ATimeoutMs: Int32): TList<TFileChange>;
  end;

  EFileWatchError = class(Exception)
  end;

implementation

type
  PByte = ^Byte;
  PInt32 = ^Int32;
  PUInt32 = ^UInt32;
  PInt64 = ^Int64;

  TTimeSpec = record
    Sec: Int64;
    NSec: Int64;
  end;

function c_close(AFd: Int32): Int32; external name 'close';

{ A NUL-terminated copy of S on the heap. }
function CString(const S: string): Pointer;
var
  I: Int;
begin
  Result := GetMem(Length(S) + 1);
  for I := 0 to Length(S) - 1 do
    PByte(UInt(Result) + UInt(I))^ := S[I];
  PByte(UInt(Result) + UInt(Length(S)))^ := 0;
end;

{$IFDEF LINUX}

{ --- inotify ---------------------------------------------------------------- }

const
  IN_MODIFY = $00000002;
  IN_ATTRIB = $00000004;
  IN_CLOSE_WRITE = $00000008;
  IN_MOVED_FROM = $00000040;
  IN_MOVED_TO = $00000080;
  IN_CREATE = $00000100;
  IN_DELETE = $00000200;
  IN_DELETE_SELF = $00000400;
  IN_MOVE_SELF = $00000800;
  IN_IGNORED = $00008000;
  IN_CLOEXEC = $00080000;
  WatchMask = IN_MODIFY or IN_ATTRIB or IN_CLOSE_WRITE or IN_MOVED_FROM or IN_MOVED_TO or
    IN_CREATE or IN_DELETE or IN_DELETE_SELF or IN_MOVE_SELF;
  POLLIN = 1;
  BufSize = 16384;

type
  TPollFd = record
    Fd: Int32;
    Events: Int16;
    REvents: Int16;
  end;

function c_inotify_init1(AFlags: Int32): Int32; external name 'inotify_init1';
function c_inotify_add_watch(AFd: Int32; APath: Pointer; AMask: UInt32): Int32;
  external name 'inotify_add_watch';
function c_inotify_rm_watch(AFd, AWd: Int32): Int32; external name 'inotify_rm_watch';
function c_poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32; external name 'poll';
function c_read(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64; external name 'read';

constructor TFileWatcher.Create();
begin
  FPaths := TDictionary<Int64, string>.Create();
  FIds := TDictionary<string, Int64>.Create();
  FQueue := c_inotify_init1(IN_CLOEXEC);
  if FQueue < 0 then
    raise EFileWatchError.Create('cannot create an inotify instance');
  FBuf := GetMem(BufSize);
end;

function TFileWatcher.Watch(const APath: string): Boolean;
var
  P: Pointer;
  Wd: Int32;
begin
  if FIds.ContainsKey(APath) then
    Exit(True);
  P := CString(APath);
  Wd := c_inotify_add_watch(FQueue, P, WatchMask);
  FreeMem(P);
  if Wd < 0 then
    Exit(False);
  FPaths[Wd] := APath;
  FIds[APath] := Wd;
  Result := True;
end;

procedure TFileWatcher.Drop(AId: Int64);
var
  Path: string;
begin
  if FPaths.TryGetValue(AId, Path) then
  begin
    FPaths.Remove(AId);
    FIds.Remove(Path);
  end;
end;

procedure TFileWatcher.Unwatch(const APath: string);
var
  Wd: Int64;
begin
  if not FIds.TryGetValue(APath, Wd) then
    Exit;
  c_inotify_rm_watch(FQueue, Int32(Wd));
  Drop(Wd);
end;

function TFileWatcher.Wait(ATimeoutMs: Int32): TList<TFileChange>;
var
  Pfd: TPollFd;
  N, Off: Int64;
  Wd: Int32;
  Mask, NameLen: UInt32;
  Path: string;
begin
  Result := TList<TFileChange>.Create();
  Pfd.Fd := FQueue;
  Pfd.Events := POLLIN;
  Pfd.REvents := 0;
  if c_poll(@Pfd, 1, ATimeoutMs) <= 0 then
    Exit;
  N := c_read(FQueue, FBuf, BufSize);
  Off := 0;
  { struct inotify_event: wd (i32), mask, cookie, len (u32), name[len]. }
  while Off + 16 <= N do
  begin
    Wd := PInt32(UInt(FBuf) + UInt(Off))^;
    Mask := PUInt32(UInt(FBuf) + UInt(Off + 4))^;
    NameLen := PUInt32(UInt(FBuf) + UInt(Off + 12))^;
    Off := Off + 16 + Int64(NameLen);
    if not FPaths.TryGetValue(Wd, Path) then
      Continue;
    if (Mask and (IN_DELETE_SELF or IN_MOVE_SELF or IN_IGNORED)) <> 0 then
    begin
      Note(Result, Path, fcDeleted);
      if (Mask and IN_IGNORED) = 0 then
        c_inotify_rm_watch(FQueue, Wd);
      Drop(Wd);
    end
    else
      Note(Result, Path, fcChanged);
  end;
end;

destructor TFileWatcher.Destroy();
begin
  if FQueue >= 0 then
    c_close(FQueue);
  if FBuf <> nil then
    FreeMem(FBuf);
  inherited Destroy();
end;

{$ELSE}

{ --- kqueue ----------------------------------------------------------------- }

const
  FILT_VNODE_U16 = $FFFC;   { EVFILT_VNODE = -4 on macOS and FreeBSD }
  EV_ADD = $0001;
  EV_CLEAR = $0020;
  NOTE_DELETE = $00000001;
  NOTE_WRITE = $00000002;
  NOTE_EXTEND = $00000004;
  NOTE_ATTRIB = $00000008;
  NOTE_RENAME = $00000020;
  NOTE_REVOKE = $00000040;
  VnodeNotes = NOTE_DELETE or NOTE_WRITE or NOTE_EXTEND or NOTE_ATTRIB or NOTE_RENAME or NOTE_REVOKE;
  GoneNotes = NOTE_DELETE or NOTE_RENAME or NOTE_REVOKE;
{$IFDEF DARWIN}
  KEVENT_SIZE = 32;         { Darwin 64-bit struct kevent (ends at udata) }
  O_WATCH = $8000;          { O_EVTONLY: an event-only descriptor }
  O_CLOEXEC = $01000000;
{$ELSE}
  KEVENT_SIZE = 64;         { FreeBSD 12+ struct kevent (with ext[4]) }
  O_WATCH = 0;              { O_RDONLY }
  O_CLOEXEC = $00100000;
{$ENDIF}
  MaxEvents = 64;

function c_kqueue(): Int32; external name 'kqueue';
function c_kevent(AKq: Int32; AChanges: Pointer; ANChanges: Int32; AEvents: Pointer; ANEvents: Int32;
  ATimeout: Pointer): Int32; external name 'kevent';
function c_open(APath: Pointer; AFlags: Int32): Int32; external name 'open';

constructor TFileWatcher.Create();
begin
  FPaths := TDictionary<Int64, string>.Create();
  FIds := TDictionary<string, Int64>.Create();
  FQueue := c_kqueue();
  if FQueue < 0 then
    raise EFileWatchError.Create('cannot create a kqueue');
  FBuf := GetMem(MaxEvents * KEVENT_SIZE);
end;

function TFileWatcher.Watch(const APath: string): Boolean;
var
  P: Pointer;
  Fd, I: Int32;
  Ev: array[0..KEVENT_SIZE - 1] of Byte;
begin
  if FIds.ContainsKey(APath) then
    Exit(True);
  P := CString(APath);
  Fd := c_open(P, O_WATCH or O_CLOEXEC);
  FreeMem(P);
  if Fd < 0 then
    Exit(False);
  for I := 0 to KEVENT_SIZE - 1 do
    Ev[I] := 0;
  { ident@0, filter@8 (i16) and flags@10 (u16) in one store, fflags@12. }
  PInt64(@Ev[0])^ := Fd;
  PUInt32(@Ev[8])^ := (UInt32(EV_ADD or EV_CLEAR) shl 16) or UInt32(FILT_VNODE_U16);
  PUInt32(@Ev[12])^ := VnodeNotes;
  if c_kevent(FQueue, @Ev[0], 1, nil, 0, nil) < 0 then
  begin
    c_close(Fd);
    Exit(False);
  end;
  FPaths[Fd] := APath;
  FIds[APath] := Fd;
  Result := True;
end;

procedure TFileWatcher.Drop(AId: Int64);
var
  Path: string;
begin
  if FPaths.TryGetValue(AId, Path) then
  begin
    FPaths.Remove(AId);
    FIds.Remove(Path);
    { Closing the descriptor removes its kevent. }
    c_close(Int32(AId));
  end;
end;

procedure TFileWatcher.Unwatch(const APath: string);
var
  Fd: Int64;
begin
  if FIds.TryGetValue(APath, Fd) then
    Drop(Fd);
end;

function TFileWatcher.Wait(ATimeoutMs: Int32): TList<TFileChange>;
var
  Ts: TTimeSpec;
  N, I: Int32;
  Ev: Pointer;
  Ident: Int64;
  Notes: UInt32;
  Path: string;
  Gone: TList<Int64>;
begin
  Result := TList<TFileChange>.Create();
  Ts.Sec := ATimeoutMs div 1000;
  Ts.NSec := Int64(ATimeoutMs mod 1000) * 1000000;
  N := c_kevent(FQueue, nil, 0, FBuf, MaxEvents, @Ts);
  Gone := TList<Int64>.Create();
  for I := 0 to N - 1 do
  begin
    Ev := Pointer(UInt(FBuf) + UInt(I * KEVENT_SIZE));
    Ident := PInt64(Ev)^;
    Notes := PUInt32(UInt(Ev) + 12)^;
    if not FPaths.TryGetValue(Ident, Path) then
      Continue;
    if (Notes and GoneNotes) <> 0 then
    begin
      Note(Result, Path, fcDeleted);
      Gone.Add(Ident);
    end
    else
      Note(Result, Path, fcChanged);
  end;
  for I := 0 to Gone.Count - 1 do
    Drop(Gone[I]);
end;

destructor TFileWatcher.Destroy();
var
  Keys: TList<Int64>;
  I: Int;
begin
  Keys := FPaths.Keys();
  for I := 0 to Keys.Count - 1 do
    c_close(Int32(Keys[I]));
  if FQueue >= 0 then
    c_close(FQueue);
  if FBuf <> nil then
    FreeMem(FBuf);
  inherited Destroy();
end;

{$ENDIF}

{ --- shared ----------------------------------------------------------------- }

{ Record a change, once per path, Deleted winning over Changed. }
procedure TFileWatcher.Note(AChanges: TList<TFileChange>; const APath: string; AKind: TFileChangeKind);
var
  I: Int;
  C: TFileChange;
begin
  for I := 0 to AChanges.Count - 1 do
    if AChanges[I].Path = APath then
    begin
      if AKind = fcDeleted then
      begin
        C := AChanges[I];
        C.Kind := fcDeleted;
        AChanges[I] := C;
      end;
      Exit;
    end;
  C.Path := APath;
  C.Kind := AKind;
  AChanges.Add(C);
end;

function TFileWatcher.Watching(const APath: string): Boolean;
begin
  Result := FIds.ContainsKey(APath);
end;

end.
