{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.streams;

{ E2E tests for the Streams RTL unit (Phase 1).
  Covers file and memory streams, virtual dispatch through abstract
  bases, and ISeekable capability discovery.  Each test compiles a
  small Blaise program against the real Streams unit and verifies
  stdout. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStreamsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_MemoryOutputStream_WriteAndReadBack;
    procedure TestRun_MemoryInputStream_ReadsBytesBack;
    procedure TestRun_FileStream_RoundTrip;
    procedure TestRun_VirtualDispatch_ThroughAbstractBase;
    procedure TestRun_ISeekable_Supports;
    procedure TestRun_BufferedFile_RoundTrip;
    procedure TestRun_BufferedOutput_FlushOnClose;
    procedure TestRun_FileOpen_MissingFile_Raises;
    procedure TestRun_TextRoundTrip_WriteLineReadLine;
    procedure TestRun_TextReader_MixedLineEndings;
    procedure TestRun_TextReader_ReadAll;
    procedure TestRun_TBuffer_WriteThenRead;
    procedure TestRun_TBuffer_TransferTo_SplitsCorrectly;
    procedure TestRun_TBuffer_IndexOf_FindsByte;
    procedure TestRun_InterfaceDispatch_ViaSupports;
    procedure TestRun_InterfaceDispatch_AsFunctionParam;
    procedure TestRun_InterfaceArg_AsExpr;
    procedure TestRun_CopyStream_MemoryToMemory;
    procedure TestRun_CopyStream_FileToFile;
  end;

implementation

procedure TE2EStreamsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-streams')
end;

const
  LE = #10;

  SrcMemOutRoundTrip = '''
    program P;
    uses Streams;
    var M: TMemoryOutputStream;
        Buf: array[0..4] of Byte;
    begin
      Buf[0] := 72;  Buf[1] := 101; Buf[2] := 108;
      Buf[3] := 108; Buf[4] := 111;
      M := TMemoryOutputStream.Create();
      try
        M.Write(@Buf[0], 5);
        WriteLn(M.ToString());
      finally
        M.Free()
      end
    end.
    ''';

  SrcMemInRoundTrip = '''
    program P;
    uses Streams;
    var M: TMemoryInputStream;
        Buf: array[0..3] of Byte;
        N: Int;
    begin
      M := TMemoryInputStream.Create('ABC');
      try
        N := M.Read(@Buf[0], 3);
        WriteLn(N);
        WriteLn(Buf[0]);
        WriteLn(Buf[1]);
        WriteLn(Buf[2]);
      finally
        M.Free()
      end
    end.
    ''';

  { Round-trip 5 bytes through TFileOutputStream and TFileInputStream
    via the system temp directory.  Uses /tmp directly to avoid pulling
    in SysUtils path helpers from this small program. }
  SrcFileRoundTrip = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Fin:  TFileInputStream;
        Buf:  array[0..15] of Byte;
        N:    Int;
        I:    Int;
    begin
      for I := 0 to 4 do Buf[I] := 65 + I;
      Fout := TFileOutputStream.Create('/tmp/blaise_streams_e2e.txt');
      try
        Fout.Write(@Buf[0], 5);
      finally
        Fout.Close();
        Fout.Free()
      end;
      for I := 0 to 15 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_streams_e2e.txt');
      try
        N := Fin.Read(@Buf[0], 16);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I]);
      finally
        Fin.Close();
        Fin.Free()
      end
    end.
    ''';

  { Demonstrate virtual dispatch through an abstract base.  TOutputStream
    declares Write as `virtual; abstract`; TMemoryOutputStream overrides
    it.  Calling Write on a TOutputStream-typed variable that actually
    holds a TMemoryOutputStream must reach the concrete implementation,
    not the abstract stub. }
  SrcVirtualDispatch = '''
    program P;
    uses Streams;
    var M:    TMemoryOutputStream;
        Base: TOutputStream;
        Buf:  array[0..3] of Byte;
    begin
      Buf[0] := 49; Buf[1] := 50; Buf[2] := 51; Buf[3] := 52;
      M := TMemoryOutputStream.Create();
      try
        Base := M;
        Base.Write(@Buf[0], 4);
        WriteLn(M.ToString());
      finally
        M.Free()
      end
    end.
    ''';

  { Buffered round-trip through file: write 10 bytes through
    TBufferedOutputStream → TFileOutputStream, read them back through
    TBufferedInputStream → TFileInputStream.  Verifies the wrappers
    correctly forward to the inner via virtual dispatch (the abstract
    TInputStream/TOutputStream slots route through the vtable to the
    file impls). }
  SrcBufferedFileRoundTrip = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Bout: TBufferedOutputStream;
        Fin:  TFileInputStream;
        Bin:  TBufferedInputStream;
        Buf:  array[0..31] of Byte;
        N, I: Int;
    begin
      for I := 0 to 9 do Buf[I] := 65 + I;
      Fout := TFileOutputStream.Create('/tmp/blaise_buf_e2e.txt');
      Bout := TBufferedOutputStream.Create(Fout);
      try
        Bout.Write(@Buf[0], 10);
      finally
        Bout.Close();
        Bout.Free()
      end;
      for I := 0 to 31 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_buf_e2e.txt');
      Bin := TBufferedInputStream.Create(Fin);
      try
        N := Bin.Read(@Buf[0], 32);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I])
      finally
        Bin.Close();
        Bin.Free()
      end
    end.
    ''';

  { Buffered output with the default 8 KiB buffer; the 5 bytes never
    fill the buffer, so they only reach the file when Close fires
    Flush.  Confirms Close-flushes-on-exit. }
  SrcBufferedFlushOnClose = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Bout: TBufferedOutputStream;
        Fin:  TFileInputStream;
        Buf:  array[0..7] of Byte;
        N, I: Int;
    begin
      Buf[0] := 1; Buf[1] := 2; Buf[2] := 3;
      Buf[3] := 4; Buf[4] := 5;
      Fout := TFileOutputStream.Create('/tmp/blaise_flush_e2e.bin');
      Bout := TBufferedOutputStream.Create(Fout);
      try
        Bout.Write(@Buf[0], 5)
        { intentionally no explicit Flush — Close must drain the buffer }
      finally
        Bout.Close();
        Bout.Free()
      end;
      for I := 0 to 7 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_flush_e2e.bin');
      try
        N := Fin.Read(@Buf[0], 8);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I])
      finally
        Fin.Close();
        Fin.Free()
      end
    end.
    ''';

  { Opening a non-existent file for reading must raise EStreamError;
    the exception handler prints a recognisable token. }
  SrcOpenMissingRaises = '''
    program P;
    uses Streams, SysUtils;
    var Fin: TFileInputStream;
    begin
      try
        Fin := TFileInputStream.Create('/tmp/blaise_does_not_exist_x42.bin');
        WriteLn('unreachable');
        Fin.Free()
      except
        on E: EStreamError do
          WriteLn('caught')
      end
    end.
    ''';

  { Full 4-layer pipeline: write three lines through
    TStreamWriter → TBufferedOutputStream → TFileOutputStream, read
    them back through TStreamReader → TBufferedInputStream →
    TFileInputStream.  Verifies the chain composes cleanly and that
    Close on the outer text writer flushes through the buffered layer
    to the file. }
  SrcTextRoundTrip = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Bout: TBufferedOutputStream;
        W:    TStreamWriter;
        Fin:  TFileInputStream;
        Bin:  TBufferedInputStream;
        R:    TStreamReader;
        Line: string;
        Count: Int;
    begin
      Fout := TFileOutputStream.Create('/tmp/blaise_text_e2e.txt');
      Bout := TBufferedOutputStream.Create(Fout);
      W    := TStreamWriter.Create(Bout);
      try
        W.WriteLine('alpha');
        W.WriteLine('beta');
        W.WriteLine('gamma')
      finally
        W.Close();
        W.Free()
      end;
      Count := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_text_e2e.txt');
      Bin := TBufferedInputStream.Create(Fin);
      R   := TStreamReader.Create(Bin);
      try
        while not R.EndOfStream() do
        begin
          Line := R.ReadLine();
          WriteLn(Line);
          Count := Count + 1
        end
      finally
        R.Close();
        R.Free()
      end;
      WriteLn(Count)
    end.
    ''';

  { In-memory mixed line endings: LF, CRLF, lone CR.  All three
    terminators must be recognised; returned lines must not include
    the terminator bytes. }
  SrcTextMixedLineEndings = '''
    program P;
    uses Streams;
    var M: TMemoryInputStream;
        R: TStreamReader;
        L: string;
    begin
      M := TMemoryInputStream.Create('aa' + #10 + 'bb' + #13#10 + 'cc' + #13 + 'dd');
      R := TStreamReader.Create(M);
      try
        while not R.EndOfStream() do
        begin
          L := R.ReadLine();
          WriteLn('[', L, ']')
        end
      finally
        R.Free()
      end
    end.
    ''';

  { ReadAll returns the entire remaining stream as one string. }
  SrcTextReadAll = '''
    program P;
    uses Streams;
    var M: TMemoryInputStream;
        R: TStreamReader;
        S: string;
    begin
      M := TMemoryInputStream.Create('hello world');
      R := TStreamReader.Create(M);
      try
        S := R.ReadAll();
        WriteLn(S);
        WriteLn(Length(S))
      finally
        R.Free()
      end
    end.
    ''';

  { TBuffer write+read round-trip.  Verifies the byte-load fix in the
    compiler's TDerefExpr lowering (loadub for ^Byte; previously loadw
    read four bytes and corrupted values). }
  SrcTBufferRoundTrip = '''
    program P;
    uses Streams;
    var B: TBuffer;
        Buf: array[0..15] of Byte;
        Dst: array[0..31] of Byte;
        I, N: Int;
    begin
      B := TBuffer.Create();
      try
        for I := 0 to 9 do Buf[I] := 65 + I;
        B.Write(@Buf[0], 10);
        WriteLn(B.Size());
        N := B.Read(@Dst[0], 32);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Dst[I]);
        WriteLn(B.Size())
      finally
        B.Free()
      end
    end.
    ''';

  { TransferTo moves a prefix of bytes from one buffer to another.
    Verifies the segment-rope split: 7 bytes move to Dst, 3 remain. }
  SrcTBufferTransferTo = '''
    program P;
    uses Streams;
    var Src, Dst: TBuffer;
        Buf: array[0..15] of Byte;
        Got: array[0..31] of Byte;
        I, N: Int;
    begin
      Src := TBuffer.Create();
      Dst := TBuffer.Create();
      try
        for I := 0 to 9 do Buf[I] := 65 + I;
        Src.Write(@Buf[0], 10);
        Src.TransferTo(Dst, 7);
        WriteLn(Src.Size());
        WriteLn(Dst.Size());
        N := Dst.Read(@Got[0], 32);
        for I := 0 to N - 1 do WriteLn(Got[I]);
        N := Src.Read(@Got[0], 32);
        for I := 0 to N - 1 do WriteLn(Got[I])
      finally
        Src.Free();
        Dst.Free()
      end
    end.
    ''';

  { IndexOf scans for a byte without consuming bytes.  Returns offset
    from the read position, or -1 if not found. }
  SrcTBufferIndexOf = '''
    program P;
    uses Streams;
    var B: TBuffer;
        Buf: array[0..15] of Byte;
        I: Int;
    begin
      B := TBuffer.Create();
      try
        for I := 0 to 9 do Buf[I] := 65 + I;
        B.Write(@Buf[0], 10);
        WriteLn(B.IndexOf(65));
        WriteLn(B.IndexOf(67));
        WriteLn(B.IndexOf(74));
        WriteLn(B.IndexOf(99));
        WriteLn(B.Size())
      finally
        B.Free()
      end
    end.
    ''';

  { Interface dispatch through Supports — query the concrete object
    for IOutputStream and call Write through the interface.  Verifies
    that the itab is correctly wired for the abstract-base hierarchy
    (TMemoryOutputStream → TOutputStream → IOutputStream). }
  SrcInterfaceViaSupports = '''
    program P;
    uses Streams;
    var M:   TMemoryOutputStream;
        Os:  IOutputStream;
        Buf: array[0..3] of Byte;
    begin
      Buf[0] := 49; Buf[1] := 50; Buf[2] := 51; Buf[3] := 52;
      M := TMemoryOutputStream.Create();
      try
        if Supports(M, IOutputStream, Os) then
          Os.Write(@Buf[0], 4);
        WriteLn(M.ToString())
      finally
        M.Free()
      end
    end.
    ''';

  { Pass an interface variable to a function expecting an
    IOutputStream parameter — exercises the two-slot fat-pointer
    parameter ABI (compiler had to be extended to pass _obj and
    _itab as two l args, alloc two var slots in the callee). }
  SrcInterfaceAsParam = '''
    program P;
    uses Streams;
    procedure WriteFour(S: IOutputStream);
    var B: array[0..3] of Byte;
    begin
      B[0] := 65; B[1] := 66; B[2] := 67; B[3] := 68;
      S.Write(@B[0], 4)
    end;
    var M:  TMemoryOutputStream;
        Os: IOutputStream;
    begin
      M := TMemoryOutputStream.Create();
      try
        if Supports(M, IOutputStream, Os) then
          WriteFour(Os);
        WriteLn(M.ToString())
      finally
        M.Free()
      end
    end.
    ''';

  SrcInterfaceArgAsExpr = '''
    program P;
    uses Streams;
    procedure WriteFour(S: IOutputStream);
    var B: array[0..3] of Byte;
    begin
      B[0] := 65; B[1] := 66; B[2] := 67; B[3] := 68;
      S.Write(@B[0], 4)
    end;
    var M: TMemoryOutputStream;
    begin
      M := TMemoryOutputStream.Create();
      try
        WriteFour(M as IOutputStream);
        WriteLn(M.ToString())
      finally
        M.Free()
      end
    end.
    ''';

  { CopyStream from one memory stream to another via the fallback
    byte-loop path (no concrete IReaderFrom/IWriterTo implementations
    yet — those are a future optimisation). }
  SrcCopyStreamMemMem = '''
    program P;
    uses Streams;
    var Src: TMemoryInputStream;
        Dst: TMemoryOutputStream;
        N:   Int64;
    begin
      Src := TMemoryInputStream.Create('hello, world!');
      Dst := TMemoryOutputStream.Create();
      try
        N := CopyStream(Src, Dst);
        WriteLn(N);
        WriteLn(Dst.ToString())
      finally
        Src.Free();
        Dst.Free()
      end
    end.
    ''';

  { CopyStream file → file.  Demonstrates the framework over real
    file streams; same fallback path as memory→memory until specific
    fast paths are added. }
  SrcCopyStreamFileFile = '''
    program P;
    uses Streams;
    var Wri:  TFileOutputStream;
        Src:  TFileInputStream;
        Dst:  TFileOutputStream;
        Vrf:  TFileInputStream;
        R:    TStreamReader;
        Buf:  array[0..15] of Byte;
        N:    Int64;
        I:    Int;
    begin
      Wri := TFileOutputStream.Create('/tmp/blaise_copy_src_e2e.txt');
      try
        for I := 0 to 9 do Buf[I] := 65 + I;
        Wri.Write(@Buf[0], 10);
      finally
        Wri.Close();
        Wri.Free()
      end;
      Src := TFileInputStream.Create('/tmp/blaise_copy_src_e2e.txt');
      Dst := TFileOutputStream.Create('/tmp/blaise_copy_dst_e2e.txt');
      try
        N := CopyStream(Src, Dst);
        WriteLn(N)
      finally
        Src.Close(); Src.Free();
        Dst.Close(); Dst.Free()
      end;
      Vrf := TFileInputStream.Create('/tmp/blaise_copy_dst_e2e.txt');
      R   := TStreamReader.Create(Vrf);
      try
        WriteLn(R.ReadAll())
      finally
        R.Free()
      end
    end.
    ''';

  { TMemoryOutputStream implements ISeekable; Supports() must return
    True and let us query the buffered byte count. }
  SrcSupportsISeekable = '''
    program P;
    uses Streams;
    var M:   TMemoryOutputStream;
        Sk:  ISeekable;
        Buf: array[0..7] of Byte;
    begin
      Buf[0] := 1; Buf[1] := 2; Buf[2] := 3;
      M := TMemoryOutputStream.Create();
      try
        M.Write(@Buf[0], 3);
        if Supports(M, ISeekable, Sk) then
          WriteLn(Sk.Size())
        else
          WriteLn('no');
      finally
        M.Free()
      end
    end.
    ''';

procedure TE2EStreamsTests.TestRun_MemoryOutputStream_WriteAndReadBack;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMemOutRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('memory stream round-trip', 'Hello' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_MemoryInputStream_ReadsBytesBack;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMemInRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('read 3 bytes A B C',
    '3' + LE + '65' + LE + '66' + LE + '67' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_FileStream_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcFileRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('file round-trip ABCDE',
    '5' + LE + '65' + LE + '66' + LE + '67' + LE + '68' + LE + '69' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_VirtualDispatch_ThroughAbstractBase;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcVirtualDispatch, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('virtual dispatch reaches concrete Write', '1234' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_ISeekable_Supports;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcSupportsISeekable, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ISeekable.Size = 3', '3' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_BufferedFile_RoundTrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBufferedFileRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('buffered round-trip A..J',
    '10' + LE + '65' + LE + '66' + LE + '67' + LE + '68' + LE + '69' + LE +
    '70' + LE + '71' + LE + '72' + LE + '73' + LE + '74' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_BufferedOutput_FlushOnClose;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBufferedFlushOnClose, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Close drained the buffer',
    '5' + LE + '1' + LE + '2' + LE + '3' + LE + '4' + LE + '5' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_FileOpen_MissingFile_Raises;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcOpenMissingRaises, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('EStreamError caught', 'caught' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TextRoundTrip_WriteLineReadLine;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTextRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('text round-trip three lines',
    'alpha' + LE + 'beta' + LE + 'gamma' + LE + '3' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TextReader_MixedLineEndings;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTextMixedLineEndings, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('LF/CRLF/CR all recognised, terminators stripped',
    '[aa]' + LE + '[bb]' + LE + '[cc]' + LE + '[dd]' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TextReader_ReadAll;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTextReadAll, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ReadAll returns entire stream',
    'hello world' + LE + '11' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TBuffer_WriteThenRead;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTBufferRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('TBuffer round-trip A..J',
    '10' + LE + '10' + LE +
    '65' + LE + '66' + LE + '67' + LE + '68' + LE + '69' + LE +
    '70' + LE + '71' + LE + '72' + LE + '73' + LE + '74' + LE +
    '0' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TBuffer_TransferTo_SplitsCorrectly;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTBufferTransferTo, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Src.Size=3, Dst.Size=7, then A..G + H..J',
    '3' + LE + '7' + LE +
    '65' + LE + '66' + LE + '67' + LE + '68' + LE +
    '69' + LE + '70' + LE + '71' + LE +
    '72' + LE + '73' + LE + '74' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_TBuffer_IndexOf_FindsByte;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTBufferIndexOf, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('IndexOf: 0, 2, 9, -1; size unchanged',
    '0' + LE + '2' + LE + '9' + LE + '-1' + LE + '10' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_InterfaceDispatch_ViaSupports;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInterfaceViaSupports, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('interface call via Supports reaches concrete Write', '1234' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_InterfaceDispatch_AsFunctionParam;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInterfaceAsParam, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('interface as function param dispatches correctly', 'ABCD' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_InterfaceArg_AsExpr;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInterfaceArgAsExpr, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('as-expr interface arg dispatches correctly', 'ABCD' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_CopyStream_MemoryToMemory;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCopyStreamMemMem, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('CopyStream mem→mem',
    '13' + LE + 'hello, world!' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_CopyStream_FileToFile;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCopyStreamFileFile, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('CopyStream file→file',
    '10' + LE + 'ABCDEFGHIJ' + LE, Output)
end;

initialization
  RegisterTest(TE2EStreamsTests)

end.
