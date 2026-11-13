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

  The watching is the platform port's (the flat _Watch* functions; see
  rtl.platform.watch.inotify for their contract): inotify on Linux, kqueue
  (EVFILT_VNODE, one descriptor per watched path) on macOS and FreeBSD, and
  ReadDirectoryChangesW on Windows, where a path is watched through its
  parent directory.  None of them forces a program to link libc. }

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
    { the platform's watch set }
    FSet: Int64;
    { watch id -> path, and back }
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

const
  { at least the 1024 the platform's contract asks for }
  MaxEvents = 1024;
  EventSize = 16;
  KindGone = 1;

type
  PInt64 = ^Int64;

function _WatchOpen(): Int64; external name '_WatchOpen';
procedure _WatchClose(ASet: Int64); external name '_WatchClose';
function _WatchAdd(ASet: Int64; const APath: string): Int64;
  external name '_WatchAdd';
procedure _WatchRemove(ASet, AId: Int64); external name '_WatchRemove';
function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32; external name '_WatchWait';

constructor TFileWatcher.Create();
begin
  FPaths := TDictionary<Int64, string>.Create();
  FIds := TDictionary<string, Int64>.Create();
  FSet := _WatchOpen();
  if FSet = -1 then
    raise EFileWatchError.Create('cannot create a file watch set');
  FBuf := GetMem(MaxEvents * EventSize);
end;

function TFileWatcher.Watch(const APath: string): Boolean;
var
  Id: Int64;
begin
  if FIds.ContainsKey(APath) then
    Exit(True);
  Id := _WatchAdd(FSet, APath);
  if Id < 0 then
    Exit(False);
  FPaths[Id] := APath;
  FIds[APath] := Id;
  Result := True;
end;

{ Forget watch AId; the platform has ended it already. }
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
  Id: Int64;
begin
  if not FIds.TryGetValue(APath, Id) then
    Exit;
  _WatchRemove(FSet, Id);
  Drop(Id);
end;

function TFileWatcher.Wait(ATimeoutMs: Int32): TList<TFileChange>;
var
  N, I: Int32;
  Id, Kind: Int64;
  Path: string;
begin
  Result := TList<TFileChange>.Create();
  N := _WatchWait(FSet, ATimeoutMs, FBuf, MaxEvents);
  for I := 0 to N - 1 do
  begin
    Id := PInt64(UInt(FBuf) + UInt(I * EventSize))^;
    Kind := PInt64(UInt(FBuf) + UInt(I * EventSize + 8))^;
    if not FPaths.TryGetValue(Id, Path) then
      Continue;
    if Kind = KindGone then
    begin
      Note(Result, Path, fcDeleted);
      Drop(Id);
    end
    else
      Note(Result, Path, fcChanged);
  end;
end;

destructor TFileWatcher.Destroy();
var
  Keys: TList<Int64>;
  I: Int;
begin
  if FSet <> -1 then
  begin
    Keys := FPaths.Keys();
    for I := 0 to Keys.Count - 1 do
      _WatchRemove(FSet, Keys[I]);
    _WatchClose(FSet);
  end;
  if FBuf <> nil then
    FreeMem(FBuf);
  inherited Destroy();
end;

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
