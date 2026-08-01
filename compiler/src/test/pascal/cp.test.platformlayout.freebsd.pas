{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.platformlayout.freebsd;

{ Tests for the FreeBSD TPlatformLayout adapter (docs/freebsd-x86_64-backend-
  design.adoc, Step 2).

  These run on the Linux CI host: they instantiate TPlatformLayoutFreeBSDX86_64
  directly (not the GPlatformLayout global, which the Linux RTL owns on a Linux
  build) and assert the FreeBSD 14.x amd64 constant values and struct stat field
  offsets.

  The struct-offset tests build a synthetic 224-byte stat buffer, plant sentinel
  Int64/Integer values at the FreeBSD offsets, and assert the accessors read them
  back.  This catches an offset typo without a FreeBSD execution environment —
  the emulation lane (Step 8) validates against a real kernel-filled struct. }

interface

uses
  blaise.testing,
  rtl.platform, rtl.platform.layout.freebsd;

type
  TFreeBSDLayoutTests = class(TTestCase)
  private
    FLayout: TPlatformLayoutFreeBSDX86_64;
  public
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { OS constants — the three that differ from Linux. }
    procedure TestO_CREAT;
    procedure TestO_TRUNC;
    procedure TestO_APPEND;
    { OS constants shared with Linux — asserted to pin them. }
    procedure TestO_RDWR;
    procedure TestS_IFDIR;
    procedure TestSEEK_END;
    procedure TestWNOHANG;
    { sysconf(3) name for the online CPU count.  FreeBSD numbers it 58; Linux
      numbers it 84, and FreeBSD's 84 is _SC_THREAD_CPUTIME, which answers with
      the POSIX option version (200112) rather than an error.  GetCPUCount would
      therefore report 200112 CPUs on a libc-hosted FreeBSD binary and the fiber
      pool would try to start that many worker threads. }
    procedure TestSC_NPROCESSORS_ONLN;
    { struct stat — the FreeBSD-specific size and field offsets. }
    procedure TestStatBufSize;
    procedure TestStatSizeOffset;
    procedure TestStatMtimeOffset;
    procedure TestStatModeOffset;
  end;

implementation

procedure TFreeBSDLayoutTests.SetUp;
begin
  FLayout := TPlatformLayoutFreeBSDX86_64.Create();
end;

procedure TFreeBSDLayoutTests.TearDown;
begin
  FLayout.Free();
end;

procedure TFreeBSDLayoutTests.TestO_CREAT;
begin
  AssertEquals('FreeBSD O_CREAT', $0200, FLayout.O_CREAT());
end;

procedure TFreeBSDLayoutTests.TestO_TRUNC;
begin
  AssertEquals('FreeBSD O_TRUNC', $0400, FLayout.O_TRUNC());
end;

procedure TFreeBSDLayoutTests.TestO_APPEND;
begin
  AssertEquals('FreeBSD O_APPEND', $0008, FLayout.O_APPEND());
end;

procedure TFreeBSDLayoutTests.TestO_RDWR;
begin
  AssertEquals('O_RDWR', 2, FLayout.O_RDWR());
end;

procedure TFreeBSDLayoutTests.TestS_IFDIR;
begin
  AssertEquals('S_IFDIR', $4000, FLayout.S_IFDIR());
end;

procedure TFreeBSDLayoutTests.TestSEEK_END;
begin
  AssertEquals('SEEK_END', 2, FLayout.SEEK_END());
end;

procedure TFreeBSDLayoutTests.TestWNOHANG;
begin
  AssertEquals('WNOHANG', 1, FLayout.WNOHANG());
end;

procedure TFreeBSDLayoutTests.TestSC_NPROCESSORS_ONLN;
begin
  AssertEquals('FreeBSD _SC_NPROCESSORS_ONLN', 58,
    FLayout.SC_NPROCESSORS_ONLN());
end;

procedure TFreeBSDLayoutTests.TestStatBufSize;
begin
  AssertEquals('FreeBSD sizeof(struct stat)', 224, FLayout.StatBufSize());
end;

{ Plant a sentinel Int64 at st_size offset (112) and read it back. }
procedure TFreeBSDLayoutTests.TestStatSizeOffset;
var
  Buf: array[0..223] of Byte;
  P: ^Int64;
  I: Integer;
begin
  for I := 0 to 223 do
    Buf[I] := 0;
  P := Pointer(PChar(@Buf[0]) + 112);
  P^ := Int64(1234567890);
  AssertEquals('st_size read at offset 112', Int64(1234567890),
    FLayout.StatSize(@Buf[0]));
end;

{ Plant a sentinel Int64 at st_mtim.tv_sec offset (64) and read it back. }
procedure TFreeBSDLayoutTests.TestStatMtimeOffset;
var
  Buf: array[0..223] of Byte;
  P: ^Int64;
  I: Integer;
begin
  for I := 0 to 223 do
    Buf[I] := 0;
  P := Pointer(PChar(@Buf[0]) + 64);
  P^ := Int64(1700000000);
  AssertEquals('st_mtim.tv_sec read at offset 64', Int64(1700000000),
    FLayout.StatMtime(@Buf[0]));
end;

{ Plant a sentinel Integer at st_mode offset (24) and read it back. }
procedure TFreeBSDLayoutTests.TestStatModeOffset;
var
  Buf: array[0..223] of Byte;
  P: ^Integer;
  I: Integer;
begin
  for I := 0 to 223 do
    Buf[I] := 0;
  P := Pointer(PChar(@Buf[0]) + 24);
  P^ := $4000;
  AssertEquals('st_mode read at offset 24', $4000, FLayout.StatMode(@Buf[0]));
end;

initialization
  RegisterTest(TFreeBSDLayoutTests);

end.
