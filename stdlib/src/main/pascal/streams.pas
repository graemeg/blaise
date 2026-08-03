{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Streams;

// Blaise RTL — stream I/O.
//
// Design summary (see docs/language-rationale.adoc for full rationale):
//
//   * One-direction streams: TInputStream and TOutputStream are separate
//     abstract roots.  Bidirectional read+write on a single handle is rare;
//     a future TRandomAccessFile can cover that case without polluting the
//     common API.
//   * Capability interfaces alongside the abstract classes.  IInputStream
//     and IOutputStream let consumers accept "anything readable / writable"
//     without forcing single inheritance, mirroring the proven IMap<K,V>
//     + TDictionary<K,V> pattern.  This is what lets TBuffer cleanly be
//     both an input source and an output sink.
//   * Wrappers own their inner stream by default (OwnsInner=True) — calling
//     Close on the outer wrapper tears down the chain.  Pass OwnsInner=False
//     to keep the inner stream alive past the wrapper's Close.
//   * Resource cleanup: ARC guarantees eventual finalisation, but the
//     idiomatic pattern is explicit Close in a try-finally so that flush
//     errors surface.

interface

uses
  SysUtils;

type
  { Exception raised by stream operations on I/O failure.

    Surfaces the underlying problem so the caller can act on it instead
    of silently losing data (this is the lesson from Rust's BufWriter
    drop-eats-errors footgun).  Errors raised:

      * Open failure — TFileInputStream / TFileOutputStream constructors
        raise when the OS rejects the open call.
      * Read failure — Read raises when the underlying read returns < 0.
      * Write failure — Write / Flush raise when the underlying write
        returns < 0 or writes fewer bytes than requested.
      * Buffered Close — when buffered data cannot be flushed.

    ARC-driven Destroy is still allowed to swallow the error (the
    finaliser cannot raise meaningfully); callers who care about
    correctness must call Close explicitly inside a try-finally. }
  EStreamError = class(Exception)
  end;

  { TFileMode — how a file is opened.

    fmOpenRead   — open existing file for reading; fail if missing.
    fmCreate     — create new file (truncate if exists) for writing.
    fmAppend     — open for appending; create if missing. }
  TFileMode = (fmOpenRead, fmCreate, fmAppend);

  { TSeekOrigin — reference point for ISeekable.Seek. }
  TSeekOrigin = (soBeginning, soCurrent, soEnd);

  { ICloseable — every stream supports Close.  Modelled on Java's Closeable
    so a future `using` block can bind to it uniformly. }
  ICloseable = interface
    procedure Close;
  end;

  { IInputStream — capability interface for byte sources.

    Read transfers up to Count bytes into the buffer at Buf and returns the
    number actually read.  A return of 0 means end-of-stream.  A short read
    (Result < Count) is permitted and does not imply EOF; callers that need
    a fixed-size read must loop. }
  IInputStream = interface(ICloseable)
    function Read(Buf: Pointer; Count: Integer): Integer;
  end;

  { IOutputStream — capability interface for byte sinks.

    Write transfers Count bytes from Buf and returns the number actually
    written.  Implementations should write all bytes or raise on error;
    short writes are reserved for non-blocking sinks (not used in v1).
    Flush forces any buffered data to the underlying device. }
  IOutputStream = interface(ICloseable)
    function Write(Buf: Pointer; Count: Integer): Integer;
    procedure Flush;
  end;

  { ISeekable — capability for streams that support random access.

    Files and in-memory buffers are ISeekable; pipes and sockets are not.
    Consumers query with the Supports() intrinsic. }
  ISeekable = interface
    function Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
    function Size: Int64;
    function Position: Int64;
  end;

  { TInputStream — abstract base class for byte sources.

    Subclasses override Read and Close.  The class exists so common stream
    implementations get an inheritance target with shared infrastructure;
    consumers that want maximum flexibility should accept IInputStream
    instead. }
  { Concrete subclasses (TFileInputStream etc.) declare the interfaces.
    The abstract bases cannot, because the interface vtable needs concrete
    method implementations and the base's are `virtual; abstract`. }
  TInputStream = class
    function Read(Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    procedure Close; virtual; abstract;
  end;

  { TOutputStream — abstract base class for byte sinks. }
  TOutputStream = class
    function Write(Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    procedure Flush; virtual; abstract;
    procedure Close; virtual; abstract;
  end;

  { TFileInputStream — reads bytes from a file on disk. }
  TFileInputStream = class(TInputStream, IInputStream, ICloseable, ISeekable)
    FFd:     Integer;     // file descriptor; -1 once closed
    FClosed: Boolean;
    constructor Create(const APath: string);
    destructor Destroy; override;
    function Read(Buf: Pointer; Count: Integer): Integer; override;
    procedure Close; override;
    function Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
    function Size: Int64;
    function Position: Int64;
  end;

  { TFileOutputStream — writes bytes to a file on disk. }
  TFileOutputStream = class(TOutputStream, IOutputStream, ICloseable, ISeekable)
    FFd:     Integer;
    FClosed: Boolean;
    constructor Create(const APath: string); overload;
    constructor Create(const APath: string; AMode: TFileMode); overload;
    destructor Destroy; override;
    function Write(Buf: Pointer; Count: Integer): Integer; override;
    procedure Flush; override;
    procedure Close; override;
    function Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
    function Size: Int64;
    function Position: Int64;
  end;

  { TMemoryInputStream — reads bytes from a Blaise string treated as bytes. }
  TMemoryInputStream = class(TInputStream, IInputStream, ICloseable, ISeekable)
    FData: string;
    FPos:  Int64;
    constructor Create(const AData: string);
    function Read(Buf: Pointer; Count: Integer): Integer; override;
    procedure Close; override;
    function Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
    function Size: Int64;
    function Position: Int64;
  end;

  { TMemoryOutputStream — accumulates bytes into an in-memory buffer.

    Use ToString to snapshot the accumulated bytes as a Blaise string. }
  TMemoryOutputStream = class(TOutputStream, IOutputStream, ICloseable, ISeekable)
    FBuf:      Pointer;   // raw byte buffer
    FCapacity: Integer;
    FSize:     Integer;
    FPos:      Integer;
    constructor Create;
    destructor Destroy; override;
    function Write(Buf: Pointer; Count: Integer): Integer; override;
    procedure Flush; override;
    procedure Close; override;
    function ToString: string; override;
    function Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
    function Size: Int64;
    function Position: Int64;
  end;

  { TBufferedInputStream — decorator that pulls from Inner in chunks.

    Reduces syscalls / per-call overhead when the consumer reads tiny
    amounts (e.g. line-by-line text parsing).  Owns Inner by default —
    closing the buffered stream also closes the inner stream.  Pass
    OwnsInner=False when the caller wants to keep the inner alive past
    the wrapper's lifetime (e.g. when the wrapper is a helper return). }
  TBufferedInputStream = class(TInputStream, IInputStream, ICloseable)
    FInner:     TInputStream;
    FOwnsInner: Boolean;
    FBuf:       Pointer;
    FBufSize:   Integer;
    FBufPos:    Integer;   // next byte to return
    FBufEnd:    Integer;   // one past last valid byte (FBufEnd >= FBufPos)
    FClosed:    Boolean;
    constructor Create(AInner: TInputStream); overload;
    constructor Create(AInner: TInputStream; ABufSize: Integer); overload;
    constructor Create(AInner: TInputStream; ABufSize: Integer;
                       AOwnsInner: Boolean); overload;
    destructor Destroy; override;
    function Read(Buf: Pointer; Count: Integer): Integer; override;
    procedure Close; override;
  end;

  { TStreamReader — text decorator that reads lines from any TInputStream.

    UTF-8 only in v1 (matches Blaise's string encoding); the Encoding
    parameter is reserved for future expansion.  Line terminators on
    read are tolerant: LF, CRLF, and lone CR are all recognised.  The
    returned line does not include the terminator.

    For efficient line reading wrap a TBufferedInputStream around the
    real source — TStreamReader makes per-byte Read calls and a raw
    TFileInputStream would be one syscall per byte.  Example:

      var R := TStreamReader.Create(
                 TBufferedInputStream.Create(
                   TFileInputStream.Create('config.txt')));

    OwnsInner=True (the default) tears the whole chain down on Close. }
  TStreamReader = class(TInputStream, IInputStream, ICloseable)
    FInner:      TInputStream;
    FOwnsInner:  Boolean;
    FAtEof:      Boolean;
    FClosed:     Boolean;
    FPending:    Byte;        { lookahead byte for CRLF handling, valid if FHasPending }
    FHasPending: Boolean;
    constructor Create(AInner: TInputStream); overload;
    constructor Create(AInner: TInputStream; AOwnsInner: Boolean); overload;
    destructor Destroy; override;
    function Read(Buf: Pointer; Count: Integer): Integer; override;
    procedure Close; override;
    function ReadLine: string;
    function ReadAll: string;
    function EndOfStream: Boolean;
  end;

  { TStreamWriter — text decorator that writes lines to any TOutputStream.

    UTF-8 only in v1.  WriteLine appends LF (a future property could
    switch to CRLF for Windows-style output).  Write writes the string
    bytes verbatim.

    OwnsInner=True closes the inner on Close.  Flush forwards to inner. }
  TStreamWriter = class(TOutputStream, IOutputStream, ICloseable)
    FInner:     TOutputStream;
    FOwnsInner: Boolean;
    FClosed:    Boolean;
    constructor Create(AInner: TOutputStream); overload;
    constructor Create(AInner: TOutputStream; AOwnsInner: Boolean); overload;
    destructor Destroy; override;
    function Write(Buf: Pointer; Count: Integer): Integer; override;
    procedure Flush; override;
    procedure Close; override;
    procedure WriteString(const S: string);
    procedure WriteLine(const S: string);
  end;

  { IReaderFrom — capability marker.

    A stream that knows how to pull bytes from a source efficiently
    (e.g. sendfile(2) between two file descriptors, or segment
    re-linking inside TBuffer) implements ReadFrom.  CopyStream
    discovers the capability at runtime via Supports() / is and
    dispatches to ReadFrom in preference to the byte-loop fallback. }
  IReaderFrom = interface
    function ReadFrom(Src: TInputStream): Int64;
  end;

  { IWriterTo — symmetrical capability marker.

    A stream that knows how to push its bytes into a sink efficiently
    implements WriteTo.  CopyStream tries IReaderFrom on the
    destination first, then IWriterTo on the source, before falling
    back to the byte-loop copy. }
  IWriterTo = interface
    function WriteTo(Dst: TOutputStream): Int64;
  end;

  { TBuffer — segmented in-memory buffer that is both source and sink.

    Internal representation is a singly-linked list of fixed-size
    segments (kSegmentSize = 8192 bytes) drawn from a module-level
    freelist.  Each segment carries Pos (next byte to read) and Limit
    (one past the last written byte) so writes append and reads
    consume from the same list without copying.

    The defining operation is TransferTo(Dst, Count): instead of
    memcpy'ing bytes from this buffer to Dst, the segments themselves
    are unlinked and re-linked onto Dst.  For multi-layer pipelines
    (decode → buffer → forward) this turns N memcpys per byte into 1,
    matching Okio's performance characteristics.

    TBuffer implements both IInputStream and IOutputStream directly
    rather than extending the abstract bases — this is the case the
    capability-interface split (over a single-class hierarchy) was
    designed for.

    TODO(threads): The segment pool is currently single-threaded.  When
    Blaise gains thread support, the pool must be guarded (per-thread
    freelist or a lock).  Audit AcquireSegment / ReleaseSegment at
    that time. }
  TBufferSegment = class
    FData:  Pointer;     { 8 KiB raw bytes; owned by the pool }
    FPos:   Integer;     { next byte to return on Read }
    FLimit: Integer;     { one past last written byte (FLimit >= FPos) }
    FNext:  TBufferSegment;
  end;

  TBuffer = class(TObject, IInputStream, IOutputStream, ICloseable)
    FHead:   TBufferSegment;  { nil if empty }
    FTail:   TBufferSegment;  { nil iff FHead is nil }
    FSize:   Int64;           { sum of (Limit - Pos) across all segments }
    FClosed: Boolean;
    constructor Create;
    destructor Destroy; override;
    function Read(Buf: Pointer; Count: Integer): Integer;
    function Write(Buf: Pointer; Count: Integer): Integer;
    procedure Flush;
    procedure Close;
    function Size: Int64;
    procedure Clear;
    { TransferTo — move up to Count bytes from this buffer into Dst by
      re-linking segments rather than copying bytes.  When a segment's
      remaining bytes exceed the requested Count, only the prefix is
      moved (via memcpy into Dst's tail segment); whole segments in
      the middle are re-linked. }
    procedure TransferTo(Dst: TBuffer; Count: Int64);
    { IndexOf — return the offset (from the read position) of the
      first occurrence of B, or -1 if not present.  Useful for line
      scanning without consuming bytes. }
    function IndexOf(B: Byte): Int64;
  end;

  { TBufferedOutputStream — decorator that accumulates writes.

    Buffers up to FBufSize bytes; on overflow (or explicit Flush) the
    buffer is forwarded to Inner.  Owns Inner by default — Close flushes,
    then closes the inner if OwnsInner is True. }
  TBufferedOutputStream = class(TOutputStream, IOutputStream, ICloseable)
    FInner:     TOutputStream;
    FOwnsInner: Boolean;
    FBuf:       Pointer;
    FBufSize:   Integer;
    FBufFill:   Integer;
    FClosed:    Boolean;
    constructor Create(AInner: TOutputStream); overload;
    constructor Create(AInner: TOutputStream; ABufSize: Integer); overload;
    constructor Create(AInner: TOutputStream; ABufSize: Integer;
                       AOwnsInner: Boolean); overload;
    destructor Destroy; override;
    function Write(Buf: Pointer; Count: Integer): Integer; override;
    procedure Flush; override;
    procedure Close; override;
  end;

{ External C primitives — file descriptor I/O.

  Declared in the interface section per Blaise convention (declaring
  externals in implementation crashes the codegen for unit consumers). }
function _FdOpenRead(Path: Pointer): Integer; external name '_FdOpenRead';
function _FdOpenWrite(Path: Pointer): Integer; external name '_FdOpenWrite';
function _FdOpenAppend(Path: Pointer): Integer; external name '_FdOpenAppend';
function _FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
  external name '_FdRead';
function _FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
  external name '_FdWrite';
function _FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
  external name '_FdSeek';
function _FdSize(Fd: Integer): Int64; external name '_FdSize';
procedure _FdClose(Fd: Integer); external name '_FdClose';

{ Raw memory helpers used by the memory streams.  memcpy is the C name (libc, or
  runtime.cstub under --static).  malloc/free/realloc bind to the RTL's own
  mmap-backed allocator (_BlaiseGetMem/_BlaiseFreeMem/_BlaiseReallocMem) rather
  than libc, so the memory streams carry no libc dependency and link into a
  --static (libc-free) build. }
function memcpy(Dst, Src: Pointer; Count: Integer): Pointer;
  external name 'memcpy';
function malloc(Count: Integer): Pointer; external name '_BlaiseGetMem';
procedure free(P: Pointer); external name '_BlaiseFreeMem';
function realloc(P: Pointer; Count: Integer): Pointer;
  external name '_BlaiseReallocMem';

{ CopyStream — transfer all readable bytes from Src to Dst.

  Returns the total byte count copied.  The implementation discovers
  capability at runtime in this preference order:

    1. Dst implements IReaderFrom   → dispatch to Dst.ReadFrom(Src).
    2. Src implements IWriterTo     → dispatch to Src.WriteTo(Dst).
    3. Fallback: an 8 KiB byte-loop copy through a stack buffer.

  v1 ships no concrete fast-path implementations — every stream uses
  the fallback.  Adding IReaderFrom to TFileOutputStream (with
  sendfile(2) on Linux), or IWriterTo to TBuffer (with TransferTo),
  is a future, non-breaking change: existing callers automatically
  pick up the speedup.

  This is Go's io.Copy idiom: callers write CopyStream(src, dst) once,
  and the framework upgrades to zero-copy when both sides cooperate. }
function CopyStream(Src: TInputStream; Dst: TOutputStream): Int64;

implementation

{ ------------------------------------------------------------------ }
{ TFileInputStream                                                    }
{ ------------------------------------------------------------------ }

constructor TFileInputStream.Create(const APath: string);
begin
  Self.FFd := _FdOpenRead(Pointer(APath));
  Self.FClosed := False;
  if Self.FFd < 0 then
  begin
    Self.FClosed := True;
    raise EStreamError.Create('Cannot open file for reading: ' + APath)
  end
end;

destructor TFileInputStream.Destroy;
begin
  if not Self.FClosed then
  begin
    _FdClose(Self.FFd);
    Self.FClosed := True
  end
end;

function TFileInputStream.Read(Buf: Pointer; Count: Integer): Integer;
var N: Integer;
begin
  if Self.FClosed then
  begin
    Result := 0;
    Exit
  end;
  N := _FdRead(Self.FFd, Buf, Count);
  if N < 0 then
    raise EStreamError.Create('File read failed');
  Result := N
end;

procedure TFileInputStream.Close;
begin
  if not Self.FClosed then
  begin
    _FdClose(Self.FFd);
    Self.FClosed := True
  end
end;

function TFileInputStream.Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
begin
  Result := _FdSeek(Self.FFd, Offset, Integer(Origin))
end;

function TFileInputStream.Size: Int64;
begin
  Result := _FdSize(Self.FFd)
end;

function TFileInputStream.Position: Int64;
begin
  Result := _FdSeek(Self.FFd, 0, Integer(soCurrent))
end;

{ ------------------------------------------------------------------ }
{ TFileOutputStream                                                   }
{ ------------------------------------------------------------------ }

constructor TFileOutputStream.Create(const APath: string);
begin
  Self.Create(APath, fmCreate)
end;

constructor TFileOutputStream.Create(const APath: string; AMode: TFileMode);
begin
  case AMode of
    fmCreate: Self.FFd := _FdOpenWrite(Pointer(APath));
    fmAppend: Self.FFd := _FdOpenAppend(Pointer(APath));
    else      Self.FFd := -1
  end;
  Self.FClosed := False;
  if Self.FFd < 0 then
  begin
    Self.FClosed := True;
    raise EStreamError.Create('Cannot open file for writing: ' + APath)
  end
end;

destructor TFileOutputStream.Destroy;
begin
  if not Self.FClosed then
  begin
    _FdClose(Self.FFd);
    Self.FClosed := True
  end
end;

function TFileOutputStream.Write(Buf: Pointer; Count: Integer): Integer;
var N: Integer;
begin
  if Self.FClosed then
  begin
    Result := 0;
    Exit
  end;
  N := _FdWrite(Self.FFd, Buf, Count);
  if N < 0 then
    raise EStreamError.Create('File write failed');
  if N < Count then
    raise EStreamError.Create('Short write to file (disk full?)');
  Result := N
end;

procedure TFileOutputStream.Flush;
begin
  // fd writes go directly to the OS; nothing to flush at this layer.
end;

procedure TFileOutputStream.Close;
begin
  if not Self.FClosed then
  begin
    _FdClose(Self.FFd);
    Self.FClosed := True
  end
end;

function TFileOutputStream.Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
begin
  Result := _FdSeek(Self.FFd, Offset, Integer(Origin))
end;

function TFileOutputStream.Size: Int64;
begin
  Result := _FdSize(Self.FFd)
end;

function TFileOutputStream.Position: Int64;
begin
  Result := _FdSeek(Self.FFd, 0, Integer(soCurrent))
end;

{ ------------------------------------------------------------------ }
{ TMemoryInputStream                                                  }
{ ------------------------------------------------------------------ }

constructor TMemoryInputStream.Create(const AData: string);
begin
  Self.FData := AData;
  Self.FPos := 0
end;

function TMemoryInputStream.Read(Buf: Pointer; Count: Integer): Integer;
var
  Remaining: Int64;
  N:         Integer;
  Src:       Pointer;
begin
  Remaining := Int64(Length(Self.FData)) - Self.FPos;
  if Remaining <= 0 then
  begin
    Result := 0;
    Exit
  end;
  if Count > Remaining then
    N := Integer(Remaining)
  else
    N := Count;
  Src := Pointer(Int64(Pointer(Self.FData)) + Self.FPos);
  memcpy(Buf, Src, N);
  Self.FPos := Self.FPos + N;
  Result := N
end;

procedure TMemoryInputStream.Close;
begin
  Self.FData := '';
  Self.FPos := 0
end;

function TMemoryInputStream.Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
var
  NewPos: Int64;
  Len:    Int64;
begin
  Len := Int64(Length(Self.FData));
  case Origin of
    soBeginning: NewPos := Offset;
    soCurrent:   NewPos := Self.FPos + Offset;
    soEnd:       NewPos := Len + Offset;
    else         NewPos := Self.FPos
  end;
  if NewPos < 0 then NewPos := 0;
  if NewPos > Len then NewPos := Len;
  Self.FPos := NewPos;
  Result := NewPos
end;

function TMemoryInputStream.Size: Int64;
begin
  Result := Int64(Length(Self.FData))
end;

function TMemoryInputStream.Position: Int64;
begin
  Result := Self.FPos
end;

{ ------------------------------------------------------------------ }
{ TMemoryOutputStream                                                 }
{ ------------------------------------------------------------------ }

constructor TMemoryOutputStream.Create;
begin
  Self.FBuf := nil;
  Self.FCapacity := 0;
  Self.FSize := 0;
  Self.FPos := 0
end;

destructor TMemoryOutputStream.Destroy;
begin
  if Self.FBuf <> nil then
  begin
    free(Self.FBuf);
    Self.FBuf := nil
  end
end;

function TMemoryOutputStream.Write(Buf: Pointer; Count: Integer): Integer;
var
  Needed: Integer;
  NewCap: Integer;
  Dst:    Pointer;
begin
  if Count <= 0 then
  begin
    Result := 0;
    Exit
  end;
  Needed := Self.FPos + Count;
  if Needed > Self.FCapacity then
  begin
    NewCap := Self.FCapacity;
    if NewCap = 0 then NewCap := 64;
    while NewCap < Needed do
      NewCap := NewCap * 2;
    Self.FBuf := realloc(Self.FBuf, NewCap);
    Self.FCapacity := NewCap
  end;
  Dst := Pointer(Int64(Self.FBuf) + Int64(Self.FPos));
  memcpy(Dst, Buf, Count);
  Self.FPos := Self.FPos + Count;
  if Self.FPos > Self.FSize then
    Self.FSize := Self.FPos;
  Result := Count
end;

procedure TMemoryOutputStream.Flush;
begin
  // No buffering at this layer.
end;

procedure TMemoryOutputStream.Close;
begin
  // The accumulated buffer is freed on Destroy; Close is a no-op so callers
  // can still read ToString afterwards.
end;

function TMemoryOutputStream.ToString: string;
var
  R:    string;
  RPtr: Pointer;
begin
  if Self.FSize = 0 then
  begin
    Result := '';
    Exit
  end;
  SetLength(R, Self.FSize);
  RPtr := Pointer(R);
  memcpy(RPtr, Self.FBuf, Self.FSize);
  Result := R
end;

function TMemoryOutputStream.Seek(Offset: Int64; Origin: TSeekOrigin): Int64;
var
  NewPos: Int64;
begin
  case Origin of
    soBeginning: NewPos := Offset;
    soCurrent:   NewPos := Int64(Self.FPos) + Offset;
    soEnd:       NewPos := Int64(Self.FSize) + Offset;
    else         NewPos := Self.FPos
  end;
  if NewPos < 0 then NewPos := 0;
  if NewPos > Int64(Self.FSize) then NewPos := Self.FSize;
  Self.FPos := Integer(NewPos);
  Result := NewPos
end;

function TMemoryOutputStream.Size: Int64;
begin
  Result := Int64(Self.FSize)
end;

function TMemoryOutputStream.Position: Int64;
begin
  Result := Int64(Self.FPos)
end;

{ ------------------------------------------------------------------ }
{ TBufferedInputStream                                                }
{ ------------------------------------------------------------------ }

const
  kDefaultBufSize = 8192;

constructor TBufferedInputStream.Create(AInner: TInputStream);
begin
  Self.Create(AInner, kDefaultBufSize, True)
end;

constructor TBufferedInputStream.Create(AInner: TInputStream; ABufSize: Integer);
begin
  Self.Create(AInner, ABufSize, True)
end;

constructor TBufferedInputStream.Create(AInner: TInputStream; ABufSize: Integer;
                                        AOwnsInner: Boolean);
begin
  Self.FInner := AInner;
  Self.FOwnsInner := AOwnsInner;
  if ABufSize < 64 then ABufSize := 64;
  Self.FBufSize := ABufSize;
  Self.FBuf := malloc(ABufSize);
  Self.FBufPos := 0;
  Self.FBufEnd := 0;
  Self.FClosed := False
end;

destructor TBufferedInputStream.Destroy;
begin
  if not Self.FClosed then
    Self.Close();
  if Self.FBuf <> nil then
  begin
    free(Self.FBuf);
    Self.FBuf := nil
  end
end;

function TBufferedInputStream.Read(Buf: Pointer; Count: Integer): Integer;
var
  Total:     Integer;
  Available: Integer;
  Take:      Integer;
  Src:       Pointer;
  Dst:       Pointer;
  N:         Integer;
begin
  if Self.FClosed or (Count <= 0) then
  begin
    Result := 0;
    Exit
  end;
  Total := 0;
  while Total < Count do
  begin
    Available := Self.FBufEnd - Self.FBufPos;
    if Available = 0 then
    begin
      { Refill from inner.  Short reads from inner are OK — they just
        give us a smaller buffer; the outer loop continues until the
        caller's Count is filled or inner returns 0 (EOF). }
      N := Self.FInner.Read(Self.FBuf, Self.FBufSize);
      if N <= 0 then Break;
      Self.FBufPos := 0;
      Self.FBufEnd := N;
      Available := N
    end;
    Take := Count - Total;
    if Take > Available then Take := Available;
    Src := Pointer(Int64(Self.FBuf) + Int64(Self.FBufPos));
    Dst := Pointer(Int64(Buf) + Int64(Total));
    memcpy(Dst, Src, Take);
    Self.FBufPos := Self.FBufPos + Take;
    Total := Total + Take
  end;
  Result := Total
end;

procedure TBufferedInputStream.Close;
begin
  if Self.FClosed then Exit;
  Self.FClosed := True;
  if Self.FOwnsInner and (Self.FInner <> nil) then
    Self.FInner.Close()
end;

{ ------------------------------------------------------------------ }
{ TBufferedOutputStream                                               }
{ ------------------------------------------------------------------ }

constructor TBufferedOutputStream.Create(AInner: TOutputStream);
begin
  Self.Create(AInner, kDefaultBufSize, True)
end;

constructor TBufferedOutputStream.Create(AInner: TOutputStream; ABufSize: Integer);
begin
  Self.Create(AInner, ABufSize, True)
end;

constructor TBufferedOutputStream.Create(AInner: TOutputStream; ABufSize: Integer;
                                         AOwnsInner: Boolean);
begin
  Self.FInner := AInner;
  Self.FOwnsInner := AOwnsInner;
  if ABufSize < 64 then ABufSize := 64;
  Self.FBufSize := ABufSize;
  Self.FBuf := malloc(ABufSize);
  Self.FBufFill := 0;
  Self.FClosed := False
end;

destructor TBufferedOutputStream.Destroy;
begin
  { ARC finaliser — best-effort flush.  If the inner write fails here
    the error is intentionally swallowed because a finaliser cannot
    meaningfully raise.  Callers who need to know whether the final
    flush succeeded must Close explicitly inside a try-finally. }
  if not Self.FClosed then
  begin
    try
      Self.Close()
    except
      on E: Exception do
        Self.FClosed := True  { absorb — finaliser cannot propagate }
    end
  end;
  if Self.FBuf <> nil then
  begin
    free(Self.FBuf);
    Self.FBuf := nil
  end
end;

function TBufferedOutputStream.Write(Buf: Pointer; Count: Integer): Integer;
var
  Remaining: Integer;
  Space:     Integer;
  Take:      Integer;
  Src:       Pointer;
  Dst:       Pointer;
  Offset:    Integer;
begin
  if Self.FClosed or (Count <= 0) then
  begin
    Result := 0;
    Exit
  end;
  Offset := 0;
  Remaining := Count;
  while Remaining > 0 do
  begin
    Space := Self.FBufSize - Self.FBufFill;
    if Space = 0 then
    begin
      Self.FInner.Write(Self.FBuf, Self.FBufFill);
      Self.FBufFill := 0;
      Space := Self.FBufSize
    end;
    Take := Remaining;
    if Take > Space then Take := Space;
    Src := Pointer(Int64(Buf) + Int64(Offset));
    Dst := Pointer(Int64(Self.FBuf) + Int64(Self.FBufFill));
    memcpy(Dst, Src, Take);
    Self.FBufFill := Self.FBufFill + Take;
    Offset := Offset + Take;
    Remaining := Remaining - Take
  end;
  Result := Count
end;

procedure TBufferedOutputStream.Flush;
begin
  if Self.FClosed then Exit;
  if Self.FBufFill > 0 then
  begin
    Self.FInner.Write(Self.FBuf, Self.FBufFill);
    Self.FBufFill := 0
  end;
  Self.FInner.Flush()
end;

procedure TBufferedOutputStream.Close;
begin
  if Self.FClosed then Exit;
  Self.Flush();
  Self.FClosed := True;
  if Self.FOwnsInner and (Self.FInner <> nil) then
    Self.FInner.Close()
end;

{ ------------------------------------------------------------------ }
{ TStreamReader                                                       }
{ ------------------------------------------------------------------ }

constructor TStreamReader.Create(AInner: TInputStream);
begin
  Self.Create(AInner, True)
end;

constructor TStreamReader.Create(AInner: TInputStream; AOwnsInner: Boolean);
begin
  Self.FInner := AInner;
  Self.FOwnsInner := AOwnsInner;
  Self.FAtEof := False;
  Self.FClosed := False;
  Self.FHasPending := False;
  Self.FPending := 0
end;

destructor TStreamReader.Destroy;
begin
  if not Self.FClosed then
    Self.Close()
end;

function TStreamReader.Read(Buf: Pointer; Count: Integer): Integer;
var
  N:    Integer;
  Dst:  Pointer;
  Rest: Integer;
  PB:   ^Byte;
begin
  { Drain the pending lookahead byte first (left over from CR handling
    in ReadLine), then defer to the inner stream for the remainder. }
  if Self.FClosed or (Count <= 0) then
  begin
    Result := 0;
    Exit
  end;
  Result := 0;
  if Self.FHasPending then
  begin
    PB := Buf;
    PB^ := Self.FPending;
    Self.FHasPending := False;
    Result := 1;
    if Count = 1 then Exit;
    Dst := Pointer(Int64(Buf) + 1);
    Rest := Count - 1
  end
  else
  begin
    Dst := Buf;
    Rest := Count
  end;
  N := Self.FInner.Read(Dst, Rest);
  if N <= 0 then
  begin
    if N = 0 then Self.FAtEof := True;
    Exit
  end;
  Result := Result + N
end;

procedure TStreamReader.Close;
begin
  if Self.FClosed then Exit;
  Self.FClosed := True;
  if Self.FOwnsInner and (Self.FInner <> nil) then
    Self.FInner.Close()
end;

function TStreamReader.ReadLine: string;
{ Read up to and including a line terminator; return the line without
  the terminator.  Tolerant: LF, CR, or CR LF all end a line.
  Returns '' at EOF (use EndOfStream to disambiguate empty line vs end). }
var
  B:       Byte;
  N:       Integer;
  Acc:     string;
  Peek:    Byte;
  PN:      Integer;
begin
  Acc := '';
  if Self.FClosed then begin Result := Acc; Exit end;
  repeat
    if Self.FHasPending then
    begin
      B := Self.FPending;
      Self.FHasPending := False;
      N := 1
    end
    else
      N := Self.FInner.Read(@B, 1);
    if N = 0 then
    begin
      Self.FAtEof := True;
      Break
    end;
    if B = 10 then        { LF — end of line }
      Break;
    if B = 13 then        { CR — peek for LF (CRLF) }
    begin
      PN := Self.FInner.Read(@Peek, 1);
      if PN = 1 then
      begin
        if Peek <> 10 then
        begin
          { Lone CR; the next byte belongs to the following line. }
          Self.FPending := Peek;
          Self.FHasPending := True
        end
      end
      else
        Self.FAtEof := True;
      Break
    end;
    Acc := Acc + Chr(B)
  until False;
  Result := Acc
end;

function TStreamReader.ReadAll: string;
var
  Buf: array[0..4095] of Byte;
  N:   Integer;
  Acc: string;
  I:   Integer;
  Chunk: string;
begin
  Acc := '';
  if Self.FClosed then begin Result := Acc; Exit end;
  repeat
    N := Self.Read(@Buf[0], 4096);
    if N <= 0 then Break;
    Chunk := '';
    for I := 0 to N - 1 do
      Chunk := Chunk + Chr(Buf[I]);
    Acc := Acc + Chunk
  until False;
  Result := Acc
end;

function TStreamReader.EndOfStream: Boolean;
var
  B: Byte;
  N: Integer;
begin
  if Self.FClosed then begin Result := True; Exit end;
  if Self.FHasPending then begin Result := False; Exit end;
  if Self.FAtEof then begin Result := True; Exit end;
  { Probe the inner stream by reading one byte; stash it as pending. }
  N := Self.FInner.Read(@B, 1);
  if N <= 0 then
  begin
    Self.FAtEof := True;
    Result := True
  end
  else
  begin
    Self.FPending := B;
    Self.FHasPending := True;
    Result := False
  end
end;

{ ------------------------------------------------------------------ }
{ TStreamWriter                                                       }
{ ------------------------------------------------------------------ }

constructor TStreamWriter.Create(AInner: TOutputStream);
begin
  Self.Create(AInner, True)
end;

constructor TStreamWriter.Create(AInner: TOutputStream; AOwnsInner: Boolean);
begin
  Self.FInner := AInner;
  Self.FOwnsInner := AOwnsInner;
  Self.FClosed := False
end;

destructor TStreamWriter.Destroy;
begin
  if not Self.FClosed then
  begin
    try
      Self.Close()
    except
      on E: Exception do
        Self.FClosed := True
    end
  end
end;

function TStreamWriter.Write(Buf: Pointer; Count: Integer): Integer;
begin
  if Self.FClosed or (Count <= 0) then
  begin
    Result := 0;
    Exit
  end;
  Result := Self.FInner.Write(Buf, Count)
end;

procedure TStreamWriter.Flush;
begin
  if Self.FClosed then Exit;
  Self.FInner.Flush()
end;

procedure TStreamWriter.Close;
begin
  if Self.FClosed then Exit;
  Self.FClosed := True;
  if Self.FOwnsInner and (Self.FInner <> nil) then
    Self.FInner.Close()
end;

procedure TStreamWriter.WriteString(const S: string);
var
  L: Integer;
begin
  L := Length(S);
  if L > 0 then
    Self.FInner.Write(Pointer(S), L)
end;

procedure TStreamWriter.WriteLine(const S: string);
var
  L:  Integer;
  LF: Byte;
begin
  L := Length(S);
  if L > 0 then
    Self.FInner.Write(Pointer(S), L);
  LF := 10;
  Self.FInner.Write(@LF, 1)
end;

{ ------------------------------------------------------------------ }
{ TBuffer — segmented in-memory buffer                                }
{ ------------------------------------------------------------------ }

const
  kSegmentSize = 8192;

{ Module-level segment freelist — LIFO recycling via intrusive FNext.

  Note: Generics.Collections.TStack<TBufferSegment> would be the
  natural fit here, but Blaise does not currently support generic
  instantiation at unit-global var scope.  The intrusive freelist
  also avoids an allocation per pool op, which matters at the rate
  TBuffer churns segments.

  TODO(threads): guard with a mutex once Blaise gains threads.  All
  AcquireSegment / ReleaseSegment sites need an audit at that time. }
var
  GSegmentPool: TBufferSegment;

function AcquireSegment: TBufferSegment;
begin
  if GSegmentPool <> nil then
  begin
    Result := GSegmentPool;
    GSegmentPool := Result.FNext;
    Result.FNext := nil;
    Result.FPos := 0;
    Result.FLimit := 0;
    Exit
  end;
  Result := TBufferSegment.Create();
  Result.FData := malloc(kSegmentSize);
  Result.FPos := 0;
  Result.FLimit := 0;
  Result.FNext := nil
end;

procedure ReleaseSegment(S: TBufferSegment);
begin
  if S = nil then Exit;
  S.FPos := 0;
  S.FLimit := 0;
  S.FNext := GSegmentPool;
  GSegmentPool := S
end;

constructor TBuffer.Create;
begin
  Self.FHead := nil;
  Self.FTail := nil;
  Self.FSize := 0;
  Self.FClosed := False
end;

destructor TBuffer.Destroy;
var
  S, N: TBufferSegment;
begin
  S := Self.FHead;
  while S <> nil do
  begin
    N := S.FNext;
    ReleaseSegment(S);
    S := N
  end;
  Self.FHead := nil;
  Self.FTail := nil;
  Self.FSize := 0
end;

procedure TBuffer.Clear;
var
  S, N: TBufferSegment;
begin
  S := Self.FHead;
  while S <> nil do
  begin
    N := S.FNext;
    ReleaseSegment(S);
    S := N
  end;
  Self.FHead := nil;
  Self.FTail := nil;
  Self.FSize := 0
end;

function TBuffer.Size: Int64;
begin
  Result := Self.FSize
end;

function TBuffer.Write(Buf: Pointer; Count: Integer): Integer;
var
  Remaining: Integer;
  Space:     Integer;
  Take:      Integer;
  Src:       Pointer;
  Dst:       Pointer;
  Offset:    Integer;
  Seg:       TBufferSegment;
begin
  if Self.FClosed or (Count <= 0) then
  begin
    Result := 0;
    Exit
  end;
  Offset := 0;
  Remaining := Count;
  while Remaining > 0 do
  begin
    { Append to tail if there is room; otherwise allocate a new segment. }
    if (Self.FTail = nil) or (Self.FTail.FLimit >= kSegmentSize) then
    begin
      Seg := AcquireSegment();
      if Self.FTail = nil then
        Self.FHead := Seg
      else
        Self.FTail.FNext := Seg;
      Self.FTail := Seg
    end;
    Space := kSegmentSize - Self.FTail.FLimit;
    Take := Remaining;
    if Take > Space then Take := Space;
    Src := Pointer(Int64(Buf) + Int64(Offset));
    Dst := Pointer(Int64(Self.FTail.FData) + Int64(Self.FTail.FLimit));
    memcpy(Dst, Src, Take);
    Self.FTail.FLimit := Self.FTail.FLimit + Take;
    Self.FSize := Self.FSize + Int64(Take);
    Offset := Offset + Take;
    Remaining := Remaining - Take
  end;
  Result := Count
end;

procedure TBuffer.Flush;
begin
  { No-op: writes land in segments immediately. }
end;

procedure TBuffer.Close;
begin
  Self.FClosed := True
end;

function TBuffer.Read(Buf: Pointer; Count: Integer): Integer;
var
  Total:     Integer;
  Available: Integer;
  Take:      Integer;
  Src:       Pointer;
  Dst:       Pointer;
  Seg:       TBufferSegment;
begin
  if Count <= 0 then
  begin
    Result := 0;
    Exit
  end;
  Total := 0;
  while (Total < Count) and (Self.FHead <> nil) do
  begin
    Available := Self.FHead.FLimit - Self.FHead.FPos;
    if Available = 0 then
    begin
      { Drained — recycle the segment and advance. }
      Seg := Self.FHead;
      Self.FHead := Seg.FNext;
      if Self.FHead = nil then Self.FTail := nil;
      ReleaseSegment(Seg);
      Continue
    end;
    Take := Count - Total;
    if Take > Available then Take := Available;
    Src := Pointer(Int64(Self.FHead.FData) + Int64(Self.FHead.FPos));
    Dst := Pointer(Int64(Buf) + Int64(Total));
    memcpy(Dst, Src, Take);
    Self.FHead.FPos := Self.FHead.FPos + Take;
    Self.FSize := Self.FSize - Int64(Take);
    Total := Total + Take
  end;
  Result := Total
end;

procedure TBuffer.TransferTo(Dst: TBuffer; Count: Int64);
{ Move up to Count bytes from this buffer into Dst's tail.

  Whole segments are unlinked from this buffer's head and re-linked
  onto Dst's tail — no bytes are copied for the common case where a
  segment is moved entirely.  If the head segment carries more bytes
  than requested, only the prefix is moved via a single memcpy into
  Dst's tail segment (a fresh segment is acquired if needed).

  Partial-prefix moves still leave the original head intact (FPos
  advanced); the segment continues to belong to this buffer. }
var
  Want:      Int64;
  HeadAvail: Int64;
  Take:      Integer;
  Seg:       TBufferSegment;
  Space:     Integer;
  Src:       Pointer;
  DstP:      Pointer;
begin
  if Count <= 0 then Exit;
  Want := Count;
  while (Want > 0) and (Self.FHead <> nil) do
  begin
    HeadAvail := Int64(Self.FHead.FLimit - Self.FHead.FPos);
    if HeadAvail = 0 then
    begin
      Seg := Self.FHead;
      Self.FHead := Seg.FNext;
      if Self.FHead = nil then Self.FTail := nil;
      ReleaseSegment(Seg);
      Continue
    end;
    if (HeadAvail <= Want) and (Self.FHead.FPos = 0) then
    begin
      { Whole-segment move — unlink and re-link.  Requires FPos = 0
        because Dst would see the segment from offset 0 and we cannot
        rewrite the segment header to keep history. }
      Seg := Self.FHead;
      Self.FHead := Seg.FNext;
      if Self.FHead = nil then Self.FTail := nil;
      Self.FSize := Self.FSize - HeadAvail;
      Seg.FNext := nil;
      if Dst.FTail = nil then
        Dst.FHead := Seg
      else
        Dst.FTail.FNext := Seg;
      Dst.FTail := Seg;
      Dst.FSize := Dst.FSize + HeadAvail;
      Want := Want - HeadAvail
    end
    else
    begin
      { Partial prefix move — memcpy into Dst's tail, then advance our
        FPos.  This is the "expensive" path; it only kicks in for
        unaligned slice boundaries (FPos > 0 or HeadAvail > Want). }
      Take := Integer(Want);
      if Int64(Take) > HeadAvail then Take := Integer(HeadAvail);
      if (Dst.FTail = nil) or (Dst.FTail.FLimit >= kSegmentSize) then
      begin
        Seg := AcquireSegment();
        if Dst.FTail = nil then
          Dst.FHead := Seg
        else
          Dst.FTail.FNext := Seg;
        Dst.FTail := Seg
      end;
      Space := kSegmentSize - Dst.FTail.FLimit;
      if Take > Space then Take := Space;
      Src := Pointer(Int64(Self.FHead.FData) + Int64(Self.FHead.FPos));
      DstP := Pointer(Int64(Dst.FTail.FData) + Int64(Dst.FTail.FLimit));
      memcpy(DstP, Src, Take);
      Self.FHead.FPos := Self.FHead.FPos + Take;
      Self.FSize := Self.FSize - Int64(Take);
      Dst.FTail.FLimit := Dst.FTail.FLimit + Take;
      Dst.FSize := Dst.FSize + Int64(Take);
      Want := Want - Int64(Take)
    end
  end
end;

function CopyStream(Src: TInputStream; Dst: TOutputStream): Int64;
var
  Buf:   array[0..8191] of Byte;
  N:     Integer;
  Total: Int64;
  RF:    IReaderFrom;
  WT:    IWriterTo;
begin
  Total := 0;
  { Capability discovery — dispatch to the optimised path when either
    side cooperates.  v1 has no concrete implementations of these
    interfaces; the checks return False and we fall through. }
  if Supports(Dst, IReaderFrom, RF) then
  begin
    Result := RF.ReadFrom(Src);
    Exit
  end;
  if Supports(Src, IWriterTo, WT) then
  begin
    Result := WT.WriteTo(Dst);
    Exit
  end;
  { Fallback: byte-loop through an 8 KiB stack buffer. }
  repeat
    N := Src.Read(@Buf[0], 8192);
    if N <= 0 then Break;
    Dst.Write(@Buf[0], N);
    Total := Total + Int64(N)
  until False;
  Result := Total
end;

function TBuffer.IndexOf(B: Byte): Int64;
{ Scan segments from head to tail looking for B; return the offset
  from the current read position, or -1 if not found.  Does not
  consume bytes. }
var
  Seg:    TBufferSegment;
  I:      Integer;
  Base:   Int64;
  PB:     ^Byte;
  Addr:   Int64;
begin
  Base := 0;
  Seg := Self.FHead;
  while Seg <> nil do
  begin
    I := Seg.FPos;
    while I < Seg.FLimit do
    begin
      Addr := Int64(Seg.FData) + Int64(I);
      PB := Pointer(Addr);
      if PB^ = B then
      begin
        Result := Base + Int64(I - Seg.FPos);
        Exit
      end;
      I := I + 1
    end;
    Base := Base + Int64(Seg.FLimit - Seg.FPos);
    Seg := Seg.FNext
  end;
  Result := -1
end;

end.
