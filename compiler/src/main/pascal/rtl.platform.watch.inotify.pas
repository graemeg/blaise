{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.watch.inotify;
// The file-change notification IO.Watch uses, on Linux, over inotify(7).
//
// Every target has one unit defining the flat _Watch* functions below, which
// BuildRTLUnitList picks: this one on Linux, rtl.platform.watch.kqueue on
// macOS and FreeBSD, rtl.platform.watch.windows on Windows.  They cannot be
// TRtlPlatform methods, because the one POSIX adapter serves all three POSIX
// targets and every RTL unit is linked into every program: the inotify names
// do not exist on the BSDs, nor kqueue on Linux.  The calls bind the bare
// names, which the libc-free profile defines as syscall leaves.
//
// The contract, the same in every unit:
//
// * _WatchOpen makes a watch set: its handle, or -1.
// * _WatchAdd watches APath, a file or a directory (not recursively): the
//   watch's id, 0 or more, or -1 when APath cannot be watched.  A file
//   changes when its contents or attributes do; a directory when an entry
//   is created, deleted or renamed.
// * _WatchWait waits up to ATimeoutMs (-1: no limit) and writes a 16-byte
//   record per event at AEvents -- the watch's id (Int64), then its kind
//   (Int64): 0 changed, 1 gone, which means the path no longer names the
//   object watched (deleted, or renamed away).  A gone event ends its
//   watch, and the id must not be removed again.  The count of records,
//   0 when the time ran out.  AMax is at least 1024.
// * _WatchRemove ends a watch, _WatchClose the set; the caller removes its
//   watches before closing the set.

interface

function _WatchOpen: Int64;
procedure _WatchClose(ASet: Int64);
function _WatchAdd(ASet: Int64; const APath: string): Int64;
procedure _WatchRemove(ASet, AId: Int64);
function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;

implementation

function c_inotify_init1(AFlags: Int32): Int32; external name 'inotify_init1';
function c_inotify_add_watch(AFd: Int32; APath: PChar; AMask: UInt32): Int32;
  external name 'inotify_add_watch';
function c_inotify_rm_watch(AFd, AWd: Int32): Int32;
  external name 'inotify_rm_watch';
function c_poll(AFds: Pointer; ANFds: Int64; ATimeout: Int32): Int32;
  external name 'poll';
function c_read(AFd: Int32; ABuf: Pointer; ACount: Int64): Int64;
  external name 'read';
function c_close(AFd: Int32): Int32; external name 'close';
function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';

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
  WATCH_MASK = IN_MODIFY or IN_ATTRIB or IN_CLOSE_WRITE or IN_MOVED_FROM or
    IN_MOVED_TO or IN_CREATE or IN_DELETE or IN_DELETE_SELF or IN_MOVE_SELF;
  GONE_MASK = IN_DELETE_SELF or IN_MOVE_SELF or IN_IGNORED;
  POLLIN = 1;
  { a struct inotify_event is at least 16 bytes, so one read of this many
    gives at most 1024 events }
  BUF_SIZE = 16384;
  EVENT_SIZE = 16;

type
  PInt16 = ^Int16;
  PInt32 = ^Int32;
  PUInt32 = ^UInt32;
  PInt64 = ^Int64;

function _WatchOpen: Int64;
var
  Fd: Int32;
begin
  Fd := c_inotify_init1(IN_CLOEXEC);
  if Fd < 0 then
    Exit(-1);
  Result := Fd;
end;

procedure _WatchClose(ASet: Int64);
begin
  if ASet >= 0 then
    c_close(Int32(ASet));
end;

function _WatchAdd(ASet: Int64; const APath: string): Int64;
var
  Wd: Int32;
begin
  if Length(APath) = 0 then
    Exit(-1);
  Wd := c_inotify_add_watch(Int32(ASet), PChar(APath), WATCH_MASK);
  if Wd < 0 then
    Exit(-1);
  Result := Wd;
end;

procedure _WatchRemove(ASet, AId: Int64);
begin
  c_inotify_rm_watch(Int32(ASet), Int32(AId));
end;

{ struct inotify_event: wd (Int32), mask, cookie and len (UInt32), then
  len bytes of name. }
function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;
var
  Pfd: array[0..7] of Byte;
  Buf: Pointer;
  N, Off: Int64;
  Wd: Int32;
  Mask, NameLen: UInt32;
  Kind: Int64;
begin
  Result := 0;
  PInt32(@Pfd[0])^ := Int32(ASet);
  PInt16(@Pfd[4])^ := POLLIN;
  PInt16(@Pfd[6])^ := 0;
  if c_poll(@Pfd[0], 1, ATimeoutMs) <= 0 then
    Exit;
  Buf := _BlaiseGetMem(BUF_SIZE);
  if Buf = nil then
    Exit;
  N := c_read(Int32(ASet), Buf, BUF_SIZE);
  Off := 0;
  while (Off + EVENT_SIZE <= N) and (Result < AMax) do
  begin
    Wd := PInt32(Buf + Off)^;
    Mask := PUInt32(Buf + Off + 4)^;
    NameLen := PUInt32(Buf + Off + 12)^;
    Off := Off + EVENT_SIZE + Int64(NameLen);
    Kind := 0;
    if (Mask and GONE_MASK) <> 0 then
    begin
      Kind := 1;
      { IN_IGNORED: the kernel has removed the watch already }
      if (Mask and IN_IGNORED) = 0 then
        c_inotify_rm_watch(Int32(ASet), Wd);
    end;
    PInt64(AEvents + Int64(Result) * 16)^ := Wd;
    PInt64(AEvents + Int64(Result) * 16 + 8)^ := Kind;
    Result := Result + 1;
  end;
  _BlaiseFreeMem(Buf);
end;

end.
