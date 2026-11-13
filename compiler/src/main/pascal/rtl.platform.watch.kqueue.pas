{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit rtl.platform.watch.kqueue;
// The file-change notification IO.Watch uses, on macOS and FreeBSD, over
// kqueue's EVFILT_VNODE: one descriptor per watched path, which is the
// watch's id.  The flat _Watch* functions and their contract are those of
// rtl.platform.watch.inotify.  The struct kevent size and the flags a
// watching descriptor is opened with differ between the two systems, and
// come from the platform layout (_KeventSize, _WatchOpenFlags).

interface

function _WatchOpen: Int64;
procedure _WatchClose(ASet: Int64);
function _WatchAdd(ASet: Int64; const APath: string): Int64;
procedure _WatchRemove(ASet, AId: Int64);
function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;

implementation

function c_kqueue: Int32; external name 'kqueue';
function c_kevent(AKq: Int32; AChanges: Pointer; ANChanges: Int32;
  AEvents: Pointer; ANEvents: Int32; ATimeout: Pointer): Int32;
  external name 'kevent';
function c_open(APath: PChar; AFlags: Int32): Int32; external name 'open';
function c_close(AFd: Int32): Int32; external name 'close';
function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer); external name '_BlaiseFreeMem';
function _KeventSize: Int32; external name '_KeventSize';
function _WatchOpenFlags: Int32; external name '_WatchOpenFlags';

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
  VNODE_NOTES = NOTE_DELETE or NOTE_WRITE or NOTE_EXTEND or NOTE_ATTRIB or
    NOTE_RENAME or NOTE_REVOKE;
  GONE_NOTES = NOTE_DELETE or NOTE_RENAME or NOTE_REVOKE;
  MAX_EVENTS = 64;
  { a struct kevent is at most this big on any target }
  KEVENT_MAX = 64;

type
  PUInt32 = ^UInt32;
  PInt64 = ^Int64;

  TTimeSpec = record
    Sec: Int64;
    NSec: Int64;
  end;

function _WatchOpen: Int64;
var
  Kq: Int32;
begin
  Kq := c_kqueue();
  if Kq < 0 then
    Exit(-1);
  Result := Kq;
end;

procedure _WatchClose(ASet: Int64);
begin
  if ASet >= 0 then
    c_close(Int32(ASet));
end;

function _WatchAdd(ASet: Int64; const APath: string): Int64;
var
  Fd: Int32;
  I: Int;
  Ev: array[0..KEVENT_MAX - 1] of Byte;
begin
  if Length(APath) = 0 then
    Exit(-1);
  Fd := c_open(PChar(APath), _WatchOpenFlags());
  if Fd < 0 then
    Exit(-1);
  for I := 0 to KEVENT_MAX - 1 do
    Ev[I] := 0;
  { ident@0, filter@8 (Int16) and flags@10 (UInt16) in one store,
    fflags@12 }
  PInt64(@Ev[0])^ := Fd;
  PUInt32(@Ev[8])^ := (UInt32(EV_ADD or EV_CLEAR) shl 16) or
    UInt32(FILT_VNODE_U16);
  PUInt32(@Ev[12])^ := VNODE_NOTES;
  if c_kevent(Int32(ASet), @Ev[0], 1, nil, 0, nil) < 0 then
  begin
    c_close(Fd);
    Exit(-1);
  end;
  Result := Fd;
end;

{ Closing the descriptor removes its kevent. }
procedure _WatchRemove(ASet, AId: Int64);
begin
  c_close(Int32(AId));
end;

{ Whether a record before record AIndex at AEvents is a gone event for
  the same descriptor. }
function GoneBefore(AEvents: Pointer; AIndex: Int32): Boolean;
var
  J: Int32;
  Ident: Int64;
begin
  Ident := PInt64(AEvents + Int64(AIndex) * 16)^;
  for J := 0 to AIndex - 1 do
    if (PInt64(AEvents + Int64(J) * 16)^ = Ident) and
       (PInt64(AEvents + Int64(J) * 16 + 8)^ = 1) then
      Exit(True);
  Result := False;
end;

function _WatchWait(ASet: Int64; ATimeoutMs: Int32; AEvents: Pointer;
  AMax: Int32): Int32;
var
  Ts: TTimeSpec;
  TsP, Buf, Ev: Pointer;
  N, I, Size, Cap: Int32;
  Ident, Kind: Int64;
  Notes: UInt32;
begin
  Result := 0;
  TsP := nil;
  if ATimeoutMs >= 0 then
  begin
    Ts.Sec := ATimeoutMs div 1000;
    Ts.NSec := Int64(ATimeoutMs mod 1000) * 1000000;
    TsP := @Ts;
  end;
  Size := _KeventSize();
  Cap := MAX_EVENTS;
  if AMax < Cap then
    Cap := AMax;
  Buf := _BlaiseGetMem(Int64(Cap) * Size);
  if Buf = nil then
    Exit;
  N := c_kevent(Int32(ASet), nil, 0, Buf, Cap, TsP);
  for I := 0 to N - 1 do
  begin
    Ev := Buf + Int64(I) * Size;
    Ident := PInt64(Ev)^;
    Notes := PUInt32(Ev + 12)^;
    Kind := 0;
    if (Notes and GONE_NOTES) <> 0 then
      Kind := 1;
    PInt64(AEvents + Int64(Result) * 16)^ := Ident;
    PInt64(AEvents + Int64(Result) * 16 + 8)^ := Kind;
    Result := Result + 1;
  end;
  { a gone watch ends here, once every event of the batch is read, and its
    descriptor is closed once though it reports twice }
  for I := 0 to Result - 1 do
    if (PInt64(AEvents + Int64(I) * 16 + 8)^ = 1) and
       not GoneBefore(AEvents, I) then
      c_close(Int32(PInt64(AEvents + Int64(I) * 16)^));
  _BlaiseFreeMem(Buf);
end;

end.
