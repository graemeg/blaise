{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.platformlayout.darwin;

{ Tests for the Darwin arm64 TPlatformLayout adapter, sibling of
  cp.test.platformlayout.freebsd.

  They run on every host: they instantiate TPlatformLayoutDarwinArm64
  directly (not the GPlatformLayout global, which the host RTL owns) and
  assert the macOS SDK constant values and the struct stat / struct dirent
  field offsets.  Every value was checked against the SDK headers with
  offsetof / sizeof on macOS 27 arm64 (2026-10-22).

  The struct-offset tests plant sentinels in a synthetic buffer and assert
  the accessors read them back, which catches an offset typo without a
  Darwin kernel.  The e2e test TE2ESysUtilsTests.TestRun_StatKnownFile_SizeMtimeMode
  checks the same accessors against a kernel-filled struct on a native
  host. }

interface

uses
  blaise.testing,
  rtl.platform, rtl.platform.layout.darwin;

type
  TDarwinLayoutTests = class(TTestCase)
  private
    FLayout: TPlatformLayoutDarwinArm64;
  public
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { OS constants: the BSD O_* creation flags, and the values shared with
      Linux and FreeBSD, pinned. }
    procedure TestO_Flags;
    procedure TestS_IFMT_IFDIR;
    procedure TestSEEK;
    procedure TestCLOCK_REALTIME_WNOHANG;
    { 58 as on FreeBSD; glibc's 84 is a different query on Darwin }
    procedure TestSC_NPROCESSORS_ONLN;
    { struct stat, 64-bit-inode layout: size and field offsets }
    procedure TestStatBufSize;
    procedure TestStatSizeOffset;
    procedure TestStatMtimeOffset;
    { st_mode is a 16-bit mode_t with nlink_t in the next two bytes: the
      read must not fold the link count into the mode }
    procedure TestStatModeOffset_IgnoresNlink;
    { struct dirent: d_reclen at 16, d_name at 21 (d_namlen precedes
      d_type, unlike Linux and FreeBSD) }
    procedure TestDirentRecLenOffset;
    procedure TestDirentNameOffset;
  end;

implementation

procedure TDarwinLayoutTests.SetUp;
begin
  FLayout := TPlatformLayoutDarwinArm64.Create();
end;

procedure TDarwinLayoutTests.TearDown;
begin
  FLayout.Free();
end;

procedure TDarwinLayoutTests.TestO_Flags;
begin
  AssertEquals('O_RDONLY', 0, FLayout.O_RDONLY());
  AssertEquals('O_WRONLY', 1, FLayout.O_WRONLY());
  AssertEquals('O_RDWR', 2, FLayout.O_RDWR());
  AssertEquals('Darwin O_CREAT', $0200, FLayout.O_CREAT());
  AssertEquals('Darwin O_TRUNC', $0400, FLayout.O_TRUNC());
  AssertEquals('Darwin O_APPEND', $0008, FLayout.O_APPEND());
end;

procedure TDarwinLayoutTests.TestS_IFMT_IFDIR;
begin
  AssertEquals('S_IFMT', $F000, FLayout.S_IFMT());
  AssertEquals('S_IFDIR', $4000, FLayout.S_IFDIR());
end;

procedure TDarwinLayoutTests.TestSEEK;
begin
  AssertEquals('SEEK_SET', 0, FLayout.SEEK_SET());
  AssertEquals('SEEK_CUR', 1, FLayout.SEEK_CUR());
  AssertEquals('SEEK_END', 2, FLayout.SEEK_END());
end;

procedure TDarwinLayoutTests.TestCLOCK_REALTIME_WNOHANG;
begin
  AssertEquals('CLOCK_REALTIME', 0, FLayout.CLOCK_REALTIME());
  AssertEquals('WNOHANG', 1, FLayout.WNOHANG());
end;

procedure TDarwinLayoutTests.TestSC_NPROCESSORS_ONLN;
begin
  AssertEquals('Darwin _SC_NPROCESSORS_ONLN', 58,
    FLayout.SC_NPROCESSORS_ONLN());
end;

procedure TDarwinLayoutTests.TestStatBufSize;
begin
  AssertEquals('Darwin sizeof(struct stat)', 144, FLayout.StatBufSize());
end;

{ Plant a sentinel Int64 at st_size offset (96) and read it back. }
procedure TDarwinLayoutTests.TestStatSizeOffset;
var
  Buf: array[0..143] of Byte;
  P: ^Int64;
  I: Integer;
begin
  for I := 0 to 143 do
    Buf[I] := 0;
  P := Pointer(PChar(@Buf[0]) + 96);
  P^ := Int64(1234567890123);
  AssertEquals('st_size read at offset 96', Int64(1234567890123),
    FLayout.StatSize(@Buf[0]));
end;

{ Plant a sentinel Int64 at st_mtimespec.tv_sec offset (48) and read it back. }
procedure TDarwinLayoutTests.TestStatMtimeOffset;
var
  Buf: array[0..143] of Byte;
  P: ^Int64;
  I: Integer;
begin
  for I := 0 to 143 do
    Buf[I] := 0;
  P := Pointer(PChar(@Buf[0]) + 48);
  P^ := Int64(1700000000);
  AssertEquals('st_mtimespec.tv_sec read at offset 48', Int64(1700000000),
    FLayout.StatMtime(@Buf[0]));
end;

{ Plant a 16-bit mode at offset 4 and a link count at offset 6. }
procedure TDarwinLayoutTests.TestStatModeOffset_IgnoresNlink;
var
  Buf: array[0..143] of Byte;
  M: ^UInt16;
  I: Integer;
begin
  for I := 0 to 143 do
    Buf[I] := 0;
  M := Pointer(PChar(@Buf[0]) + 4);
  M^ := $41ED;
  M := Pointer(PChar(@Buf[0]) + 6);
  M^ := 3;
  AssertEquals('st_mode read at offset 4, 16 bits', $41ED,
    FLayout.StatMode(@Buf[0]));
end;

procedure TDarwinLayoutTests.TestDirentRecLenOffset;
var
  Buf: array[0..63] of Byte;
  W: ^UInt16;
  I: Integer;
begin
  for I := 0 to 63 do
    Buf[I] := 0;
  W := Pointer(PChar(@Buf[0]) + 16);
  W^ := 40;
  AssertEquals('d_reclen read at offset 16', 40,
    FLayout.DirentRecLen(@Buf[0]));
end;

procedure TDarwinLayoutTests.TestDirentNameOffset;
var
  Buf: array[0..63] of Byte;
begin
  AssertTrue('d_name at offset 21',
    PChar(FLayout.DirentName(@Buf[0])) = PChar(@Buf[0]) + 21);
end;

initialization
  RegisterTest(TDarwinLayoutTests);

end.
