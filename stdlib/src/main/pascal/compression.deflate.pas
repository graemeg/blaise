{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Compression.Deflate - the DEFLATE format (RFC 1951) and its zlib wrapper
  (RFC 1950), in pure Pascal.

    Packed := Deflate(Data);              // raw DEFLATE, as zip entries use
    Data   := Inflate(Packed);
    Packed := ZlibCompress(Data);         // zlib stream, as PNG and HTTP use
    Data   := ZlibDecompress(Packed);

  Data is a string of raw bytes throughout, as in Security.Crypto.  Gzip
  (Compression.Gzip) and zip archives (Compression.Zip) are built on this
  unit.

  Inflate decodes stored, fixed-Huffman and dynamic-Huffman blocks.  It
  refuses malformed input with ECompressionError rather than returning
  partial or wrong data: a truncated stream, a reserved block type, a stored
  block whose length check fails, an over-subscribed or unusable Huffman
  code, or a match that reaches back before the start of the output.

  Deflate is an LZ77 compressor with hash chains over the 32 KiB window.
  Each block is written in whichever of the three block types is smallest
  for it, so incompressible data costs five bytes per 64 KiB, not more.
  ALevel trades speed for ratio as zlib's does: 0 stores without
  compressing, 1 searches least, 9 most; the default is 6.  The output is a
  valid stream any inflater reads, but not byte-identical to zlib's.

  Not supported: preset dictionaries (a zlib stream that needs one is
  refused) and streaming: input and output are whole strings. }

unit Compression.Deflate;

interface

uses
  SysUtils;

type
  { Raised for malformed or unsupported compressed data. }
  ECompressionError = class(Exception)
  end;

{ Compresses AData as a raw DEFLATE stream.  ALevel is 0 (store) to 9
  (smallest); values outside that range are clamped. }
function Deflate(const AData: string; ALevel: Int = 6): string;

{ Decompresses the raw DEFLATE stream AData.  Bytes after the final block
  are ignored. }
function Inflate(const AData: string): string;

{ Decompresses the raw DEFLATE stream that starts at byte offset AStart of
  AData (0-based).  AEnd receives the offset of the first byte after the
  stream's final block, where any following data (a gzip trailer, the next
  member) begins. }
function InflateAt(const AData: string; AStart: Int; out AEnd: Int): string;

{ Compresses AData as a zlib stream: a two-byte header, raw DEFLATE data
  and the Adler-32 of AData. }
function ZlibCompress(const AData: string; ALevel: Int = 6): string;

{ Decompresses the zlib stream AData, verifying its header and Adler-32.
  A stream that needs a preset dictionary raises ECompressionError. }
function ZlibDecompress(const AData: string): string;

implementation

uses
  StrUtils, Compression.Checksums;

const
  MAX_BITS = 15;
  WINDOW_SIZE = 32768;
  WINDOW_MASK = 32767;
  MIN_MATCH = 3;
  MAX_MATCH = 258;
  MAX_STORED = 65535;

  LENGTH_BASE: array[0..28] of Int32 = (
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
    35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258);
  LENGTH_EXTRA: array[0..28] of Int32 = (
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
    3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0);
  DIST_BASE: array[0..29] of Int32 = (
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
    257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
    8193, 12289, 16385, 24577);
  DIST_EXTRA: array[0..29] of Int32 = (
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
    7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13);
  { The order code-length code lengths are sent in (RFC 1951 3.2.7). }
  CLEN_ORDER: array[0..18] of Int32 = (
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15);

type
  TIntArray = array of Int32;
  TDeflateBytes = array of Byte;

procedure Fail(const AMsg: string);
begin
  raise ECompressionError.Create('Invalid deflate data: ' + AMsg);
end;

{ The low ABits bits of ACode in reverse order: Huffman codes are packed
  most-significant bit first into an otherwise LSB-first bit stream. }
function ReverseBits(ACode, ABits: Int): Int;
var
  I: Int;
begin
  Result := 0;
  for I := 1 to ABits do
  begin
    Result := (Result shl 1) or (ACode and 1);
    ACode := ACode shr 1;
  end;
end;

{ Canonical codes (RFC 1951 3.2.2) for ACount symbols with code lengths
  ALens.  Returns False when the lengths over-subscribe the code space. }
function CanonicalCodes(const ALens: TIntArray; ACount: Int;
  var ACodes: TIntArray): Boolean;
var
  BlCount: array[0..15] of Int32;
  NextCode: array[0..15] of Int32;
  I, Code, Left: Int;
begin
  for I := 0 to MAX_BITS do
    BlCount[I] := 0;
  for I := 0 to ACount - 1 do
    BlCount[ALens[I]] := BlCount[ALens[I]] + 1;
  BlCount[0] := 0;
  Left := 1;
  for I := 1 to MAX_BITS do
  begin
    Left := Left * 2 - BlCount[I];
    if Left < 0 then
      Exit(False);
  end;
  Code := 0;
  NextCode[0] := 0;
  for I := 1 to MAX_BITS do
  begin
    Code := (Code + BlCount[I - 1]) shl 1;
    NextCode[I] := Code;
  end;
  SetLength(ACodes, ACount);
  for I := 0 to ACount - 1 do
    if ALens[I] <> 0 then
    begin
      ACodes[I] := NextCode[ALens[I]];
      NextCode[ALens[I]] := NextCode[ALens[I]] + 1;
    end
    else
      ACodes[I] := 0;
  Result := True;
end;

{ ------------------------------------------------------------------ }
{ Inflate                                                             }
{ ------------------------------------------------------------------ }

type
  { A Huffman decoding table indexed by the next FBits input bits (LSB
    first).  Each entry is (symbol shl 4) or code length; 0 marks a bit
    pattern no code uses. }
  THuffDecoder = class
    FTable: TIntArray;
    FBits: Int;
    constructor Create(const ALens: TIntArray; ACount: Int);
  end;

  TInflater = class
    FSrc: string;
    FPos: Int;          { next source byte to load into the bit buffer }
    FLen: Int;
    FBitBuf: UInt64;
    FBitCnt: Int;
    FPadBits: Int;      { zero bits loaded from beyond the end of FSrc }
    FOut: TDeflateBytes;
    FOutLen: Int;
    constructor Create(const ASrc: string; AStart: Int);
    procedure NeedBits(N: Int);
    procedure DropBits(N: Int);
    function GetBits(N: Int): Int;
    function Decode(H: THuffDecoder): Int;
    procedure Grow(AExtra: Int);
    procedure StoredBlock;
    procedure CodesBlock(ALit, ADist: THuffDecoder);
    procedure DynamicBlock;
    procedure Run;
    function EndOffset: Int;
    function Output: string;
  end;

constructor THuffDecoder.Create(const ALens: TIntArray; ACount: Int);
var
  Codes: TIntArray;
  I, J, Step, Size: Int;
begin
  inherited Create();
  if not CanonicalCodes(ALens, ACount, Codes) then
    Fail('over-subscribed Huffman code');
  Self.FBits := 1;
  for I := 0 to ACount - 1 do
    if ALens[I] > Self.FBits then
      Self.FBits := ALens[I];
  Size := 1 shl Self.FBits;
  SetLength(Self.FTable, Size);
  for I := 0 to Size - 1 do
    Self.FTable[I] := 0;
  for I := 0 to ACount - 1 do
    if ALens[I] <> 0 then
    begin
      J := ReverseBits(Codes[I], ALens[I]);
      Step := 1 shl ALens[I];
      while J < Size do
      begin
        Self.FTable[J] := (I shl 4) or ALens[I];
        J := J + Step;
      end;
    end;
end;

constructor TInflater.Create(const ASrc: string; AStart: Int);
begin
  inherited Create();
  Self.FSrc := ASrc;
  Self.FPos := AStart;
  Self.FLen := Length(ASrc);
  Self.FBitBuf := 0;
  Self.FBitCnt := 0;
  Self.FPadBits := 0;
  SetLength(Self.FOut, 4096);
  Self.FOutLen := 0;
end;

procedure TInflater.NeedBits(N: Int);
begin
  while Self.FBitCnt < N do
  begin
    if Self.FPos < Self.FLen then
    begin
      Self.FBitBuf := Self.FBitBuf or
        (UInt64(Byte(Self.FSrc[Self.FPos])) shl Self.FBitCnt);
      Self.FPos := Self.FPos + 1;
    end
    else
      { Past the end: load zeros so a decode table can be indexed, and
        count them so consuming any of them is caught as truncation. }
      Self.FPadBits := Self.FPadBits + 8;
    Self.FBitCnt := Self.FBitCnt + 8;
  end;
end;

procedure TInflater.DropBits(N: Int);
begin
  Self.FBitBuf := Self.FBitBuf shr N;
  Self.FBitCnt := Self.FBitCnt - N;
  if Self.FBitCnt < Self.FPadBits then
    Fail('unexpected end of data');
end;

function TInflater.GetBits(N: Int): Int;
begin
  if N = 0 then
    Exit(0);
  Self.NeedBits(N);
  Result := Int(Self.FBitBuf and ((UInt64(1) shl N) - 1));
  Self.DropBits(N);
end;

function TInflater.Decode(H: THuffDecoder): Int;
var
  E: Int;
begin
  Self.NeedBits(H.FBits);
  E := H.FTable[Int(Self.FBitBuf and UInt64((1 shl H.FBits) - 1))];
  if E = 0 then
  begin
    { A pattern no code uses: truncation if it ran into the padding,
      otherwise a bad (incomplete) code. }
    if Self.FPadBits > 0 then
      Fail('unexpected end of data');
    Fail('invalid Huffman code');
  end;
  Self.DropBits(E and 15);
  Result := E shr 4;
end;

procedure TInflater.Grow(AExtra: Int);
var
  NewCap: Int;
begin
  if Self.FOutLen + AExtra <= Length(Self.FOut) then
    Exit;
  NewCap := Length(Self.FOut) * 2;
  while NewCap < Self.FOutLen + AExtra do
    NewCap := NewCap * 2;
  SetLength(Self.FOut, NewCap);
end;

procedure TInflater.StoredBlock;
var
  Len, NLen: Int;
begin
  { Skip to a byte boundary; LEN and NLEN follow, then LEN raw bytes. }
  Self.DropBits(Self.FBitCnt mod 8);
  Len := Self.GetBits(16);
  NLen := Self.GetBits(16);
  if Len <> (NLen xor $FFFF) then
    Fail('stored block length check failed');
  Self.Grow(Len);
  { Whole bytes already in the bit buffer come first. }
  while (Len > 0) and (Self.FBitCnt >= 8) do
  begin
    Self.FOut[Self.FOutLen] := Byte(Self.GetBits(8));
    Self.FOutLen := Self.FOutLen + 1;
    Len := Len - 1;
  end;
  if Self.FPos + Len > Self.FLen then
    Fail('unexpected end of data');
  while Len > 0 do
  begin
    Self.FOut[Self.FOutLen] := Byte(Self.FSrc[Self.FPos]);
    Self.FOutLen := Self.FOutLen + 1;
    Self.FPos := Self.FPos + 1;
    Len := Len - 1;
  end;
end;

procedure TInflater.CodesBlock(ALit, ADist: THuffDecoder);
var
  Sym, Len, Dist, I, From: Int;
begin
  repeat
    Sym := Self.Decode(ALit);
    if Sym < 256 then
    begin
      Self.Grow(1);
      Self.FOut[Self.FOutLen] := Byte(Sym);
      Self.FOutLen := Self.FOutLen + 1;
    end
    else if Sym > 256 then
    begin
      Sym := Sym - 257;
      if Sym > 28 then
        Fail('invalid length symbol');
      Len := LENGTH_BASE[Sym] + Self.GetBits(LENGTH_EXTRA[Sym]);
      Sym := Self.Decode(ADist);
      if Sym > 29 then
        Fail('invalid distance symbol');
      Dist := DIST_BASE[Sym] + Self.GetBits(DIST_EXTRA[Sym]);
      if Dist > Self.FOutLen then
        Fail('distance too far back');
      Self.Grow(Len);
      From := Self.FOutLen - Dist;
      { Byte by byte: a match may overlap the bytes it is producing. }
      for I := 0 to Len - 1 do
        Self.FOut[Self.FOutLen + I] := Self.FOut[From + I];
      Self.FOutLen := Self.FOutLen + Len;
    end;
  until Sym = 256;
end;

procedure TInflater.DynamicBlock;
var
  NLit, NDist, NCodeLen, I, Sym, Rep, Prev, Total: Int;
  Lens, LitLens, DistLens: TIntArray;
  CodeLenDec, LitDec, DistDec: THuffDecoder;
begin
  NLit := Self.GetBits(5) + 257;
  NDist := Self.GetBits(5) + 1;
  NCodeLen := Self.GetBits(4) + 4;
  if (NLit > 286) or (NDist > 30) then
    Fail('too many length or distance codes');

  SetLength(Lens, 19);
  for I := 0 to 18 do
    Lens[I] := 0;
  for I := 0 to NCodeLen - 1 do
    Lens[CLEN_ORDER[I]] := Self.GetBits(3);
  CodeLenDec := THuffDecoder.Create(Lens, 19);

  { The literal/length and distance code lengths form one sequence, and a
    repeat may run from one into the other. }
  Total := NLit + NDist;
  SetLength(Lens, Total);
  I := 0;
  while I < Total do
  begin
    Sym := Self.Decode(CodeLenDec);
    if Sym < 16 then
    begin
      Lens[I] := Sym;
      I := I + 1;
    end
    else
    begin
      Prev := 0;
      if Sym = 16 then
      begin
        if I = 0 then
          Fail('repeat with no previous length');
        Prev := Lens[I - 1];
        Rep := 3 + Self.GetBits(2);
      end
      else if Sym = 17 then
        Rep := 3 + Self.GetBits(3)
      else
        Rep := 11 + Self.GetBits(7);
      if I + Rep > Total then
        Fail('code lengths overrun');
      while Rep > 0 do
      begin
        Lens[I] := Prev;
        I := I + 1;
        Rep := Rep - 1;
      end;
    end;
  end;
  CodeLenDec.Free();
  if Lens[256] = 0 then
    Fail('no end-of-block code');

  SetLength(LitLens, NLit);
  for I := 0 to NLit - 1 do
    LitLens[I] := Lens[I];
  SetLength(DistLens, NDist);
  for I := 0 to NDist - 1 do
    DistLens[I] := Lens[NLit + I];
  LitDec := THuffDecoder.Create(LitLens, NLit);
  DistDec := THuffDecoder.Create(DistLens, NDist);
  try
    Self.CodesBlock(LitDec, DistDec);
  finally
    LitDec.Free();
    DistDec.Free();
  end;
end;

procedure TInflater.Run;
var
  IsFinal: Boolean;
  BType, I: Int;
  Lens: TIntArray;
  FixedLit, FixedDist: THuffDecoder;
begin
  FixedLit := nil;
  FixedDist := nil;
  try
    repeat
      IsFinal := Self.GetBits(1) = 1;
      BType := Self.GetBits(2);
      if BType = 0 then
        Self.StoredBlock()
      else if BType = 1 then
      begin
        if FixedLit = nil then
        begin
          { RFC 1951 3.2.6.  Symbols 286, 287 and distances 30, 31 take
            part in the code but never appear in valid data. }
          SetLength(Lens, 288);
          for I := 0 to 143 do Lens[I] := 8;
          for I := 144 to 255 do Lens[I] := 9;
          for I := 256 to 279 do Lens[I] := 7;
          for I := 280 to 287 do Lens[I] := 8;
          FixedLit := THuffDecoder.Create(Lens, 288);
          SetLength(Lens, 32);
          for I := 0 to 31 do Lens[I] := 5;
          FixedDist := THuffDecoder.Create(Lens, 32);
        end;
        Self.CodesBlock(FixedLit, FixedDist);
      end
      else if BType = 2 then
        Self.DynamicBlock()
      else
        Fail('reserved block type');
    until IsFinal;
  finally
    if FixedLit <> nil then
    begin
      FixedLit.Free();
      FixedDist.Free();
    end;
  end;
end;

function TInflater.EndOffset: Int;
begin
  { Whole bytes still in the bit buffer were loaded but not used. }
  Result := Self.FPos - (Self.FBitCnt - Self.FPadBits) div 8;
end;

function BytesToString(const ABytes: TDeflateBytes; ACount: Int): string;
var
  P: ^Byte;
begin
  Result := '';
  if ACount = 0 then
    Exit;
  SetLength(Result, ACount);
  P := Pointer(Result);
  Move(ABytes[0], P^, ACount);
end;

function TInflater.Output: string;
begin
  Result := BytesToString(Self.FOut, Self.FOutLen);
end;

function InflateAt(const AData: string; AStart: Int; out AEnd: Int): string;
var
  Inf: TInflater;
begin
  if (AStart < 0) or (AStart > Length(AData)) then
    raise ECompressionError.Create('Inflate start offset out of range');
  Inf := TInflater.Create(AData, AStart);
  try
    Inf.Run();
    AEnd := Inf.EndOffset();
    Result := Inf.Output();
  finally
    Inf.Free();
  end;
end;

function Inflate(const AData: string): string;
var
  EndPos: Int;
begin
  Result := InflateAt(AData, 0, EndPos);
end;

{ ------------------------------------------------------------------ }
{ Deflate                                                             }
{ ------------------------------------------------------------------ }

const
  { Symbols gathered before a block is closed and encoded. }
  BLOCK_SYMBOLS = 16384;
  HASH_BITS = 15;
  HASH_SIZE = 32768;
  HASH_MASK = 32767;

type
  { Bits are packed LSB first into whole bytes appended to FOut. }
  TBitWriter = class
    FOut: TStringBuilder;
    FBuf: UInt64;
    FCnt: Int;
    constructor Create;
    destructor Destroy; override;
    procedure PutBits(AValue: Int; ABits: Int);
    { Huffman codes go out most-significant bit first. }
    procedure PutCode(ACode: Int; ABits: Int);
    procedure AlignToByte;
    function Finish: string;
  end;

  TDeflater = class
    FSrc: string;
    FLen: Int;
    FMaxChain: Int;
    FNiceLen: Int;
    FHead: TIntArray;
    FPrev: TIntArray;
    { The current block: FSymDist[i] = 0 for a literal FSymVal[i], otherwise
      a match of length FSymVal[i] at that distance. }
    FSymVal: TIntArray;
    FSymDist: TIntArray;
    FSymCount: Int;
    FBlockStart: Int;
    FLitFreq: TIntArray;
    FDistFreq: TIntArray;
    FLenCode: TIntArray;    { match length 3..258 -> symbol index 0..28 }
    FW: TBitWriter;
    constructor Create(const ASrc: string; ALevel: Int);
    destructor Destroy; override;
    function HashAt(APos: Int): Int;
    procedure Insert(APos: Int);
    function LongestMatch(APos: Int; out ADist: Int): Int;
    procedure AddSymbol(AVal, ADist: Int);
    procedure FlushBlock(AEnd: Int; AFinal: Boolean);
    procedure WriteStored(AStart, AEnd: Int; AFinal: Boolean);
    procedure WriteCodes(const ALitLens, ALitCodes, ADistLens, ADistCodes: TIntArray);
    function Compress: string;
  end;

constructor TBitWriter.Create;
begin
  inherited Create();
  Self.FOut := TStringBuilder.Create();
  Self.FBuf := 0;
  Self.FCnt := 0;
end;

destructor TBitWriter.Destroy;
begin
  Self.FOut.Free();
  inherited Destroy();
end;

procedure TBitWriter.PutBits(AValue: Int; ABits: Int);
begin
  Self.FBuf := Self.FBuf or (UInt64(AValue) shl Self.FCnt);
  Self.FCnt := Self.FCnt + ABits;
  while Self.FCnt >= 8 do
  begin
    Self.FOut.AppendByte(Byte(Self.FBuf and $FF));
    Self.FBuf := Self.FBuf shr 8;
    Self.FCnt := Self.FCnt - 8;
  end;
end;

procedure TBitWriter.PutCode(ACode: Int; ABits: Int);
begin
  Self.PutBits(ReverseBits(ACode, ABits), ABits);
end;

procedure TBitWriter.AlignToByte;
begin
  if Self.FCnt > 0 then
    Self.PutBits(0, 8 - Self.FCnt);
end;

function TBitWriter.Finish: string;
begin
  Self.AlignToByte();
  Result := Self.FOut.ToString();
end;

{ Code lengths, at most ALimit bits, for the ACount symbols with frequencies
  AFreq: a Huffman code built by repeatedly joining the two least frequent
  subtrees.  When a length exceeds ALimit the frequencies are flattened
  (halved, rounding up) and the code rebuilt; equal frequencies give a
  balanced tree, so this always ends.  Fewer than two used symbols are
  padded to two so that every code written is complete. }
procedure BuildLengths(const AFreq: TIntArray; ACount, ALimit: Int;
  var ALens: TIntArray);
var
  Freq, Weight, Parent: TIntArray;
  Alive: array of Boolean;
  N, I, A, B, Used, MaxLen, D, K: Int;
begin
  SetLength(Freq, ACount);
  Used := 0;
  for I := 0 to ACount - 1 do
  begin
    Freq[I] := AFreq[I];
    if Freq[I] > 0 then
      Used := Used + 1;
  end;
  I := 0;
  while (Used < 2) and (I < ACount) do
  begin
    if Freq[I] = 0 then
    begin
      Freq[I] := 1;
      Used := Used + 1;
    end;
    I := I + 1;
  end;

  SetLength(ALens, ACount);
  repeat
    { Nodes 0..ACount-1 are leaves, internal nodes follow. }
    SetLength(Weight, ACount * 2);
    SetLength(Parent, ACount * 2);
    SetLength(Alive, ACount * 2);
    for I := 0 to ACount * 2 - 1 do
    begin
      Parent[I] := -1;
      Alive[I] := False;
    end;
    for I := 0 to ACount - 1 do
    begin
      Weight[I] := Freq[I];
      Alive[I] := Freq[I] > 0;
    end;
    N := ACount;
    for K := 1 to Used - 1 do
    begin
      A := -1;
      B := -1;
      for I := 0 to N - 1 do
        if Alive[I] then
        begin
          if (A < 0) or (Weight[I] < Weight[A]) then
          begin
            B := A;
            A := I;
          end
          else if (B < 0) or (Weight[I] < Weight[B]) then
            B := I;
        end;
      Weight[N] := Weight[A] + Weight[B];
      Alive[N] := True;
      Alive[A] := False;
      Alive[B] := False;
      Parent[A] := N;
      Parent[B] := N;
      N := N + 1;
    end;
    MaxLen := 0;
    for I := 0 to ACount - 1 do
    begin
      ALens[I] := 0;
      if Freq[I] > 0 then
      begin
        D := 0;
        K := I;
        while Parent[K] >= 0 do
        begin
          K := Parent[K];
          D := D + 1;
        end;
        ALens[I] := D;
        if D > MaxLen then
          MaxLen := D;
      end;
    end;
    if MaxLen > ALimit then
      for I := 0 to ACount - 1 do
        if Freq[I] > 0 then
          Freq[I] := (Freq[I] + 1) div 2;
  until MaxLen <= ALimit;
end;

{ The distance symbol (0..29) for a match distance 1..32768. }
function DistSymbol(ADist: Int): Int;
var
  Lo, Hi, Mid: Int;
begin
  Lo := 0;
  Hi := 29;
  while Lo < Hi do
  begin
    Mid := (Lo + Hi + 1) div 2;
    if DIST_BASE[Mid] <= ADist then
      Lo := Mid
    else
      Hi := Mid - 1;
  end;
  Result := Lo;
end;

constructor TDeflater.Create(const ASrc: string; ALevel: Int);
var
  I, S: Int;
begin
  inherited Create();
  Self.FSrc := ASrc;
  Self.FLen := Length(ASrc);
  case ALevel of
    1: begin Self.FMaxChain := 4; Self.FNiceLen := 16; end;
    2: begin Self.FMaxChain := 8; Self.FNiceLen := 32; end;
    3: begin Self.FMaxChain := 16; Self.FNiceLen := 32; end;
    4: begin Self.FMaxChain := 24; Self.FNiceLen := 64; end;
    5: begin Self.FMaxChain := 32; Self.FNiceLen := 128; end;
    6: begin Self.FMaxChain := 64; Self.FNiceLen := 128; end;
    7: begin Self.FMaxChain := 128; Self.FNiceLen := 258; end;
    8: begin Self.FMaxChain := 256; Self.FNiceLen := 258; end;
  else
    begin Self.FMaxChain := 1024; Self.FNiceLen := 258; end;
  end;
  SetLength(Self.FHead, HASH_SIZE);
  for I := 0 to HASH_SIZE - 1 do
    Self.FHead[I] := -1;
  SetLength(Self.FPrev, WINDOW_SIZE);
  SetLength(Self.FSymVal, BLOCK_SYMBOLS);
  SetLength(Self.FSymDist, BLOCK_SYMBOLS);
  Self.FSymCount := 0;
  Self.FBlockStart := 0;
  SetLength(Self.FLitFreq, 286);
  SetLength(Self.FDistFreq, 30);
  for I := 0 to 285 do
    Self.FLitFreq[I] := 0;
  for I := 0 to 29 do
    Self.FDistFreq[I] := 0;
  SetLength(Self.FLenCode, MAX_MATCH + 1);
  S := 0;
  for I := MIN_MATCH to MAX_MATCH do
  begin
    while (S < 28) and (LENGTH_BASE[S + 1] <= I) do
      S := S + 1;
    Self.FLenCode[I] := S;
  end;
  Self.FW := TBitWriter.Create();
end;

destructor TDeflater.Destroy;
begin
  Self.FW.Free();
  inherited Destroy();
end;

function TDeflater.HashAt(APos: Int): Int;
begin
  Result := ((Byte(Self.FSrc[APos]) shl 10) xor (Byte(Self.FSrc[APos + 1]) shl 5)
    xor Byte(Self.FSrc[APos + 2])) and HASH_MASK;
end;

procedure TDeflater.Insert(APos: Int);
var
  H: Int;
begin
  if APos + MIN_MATCH > Self.FLen then
    Exit;
  H := Self.HashAt(APos);
  Self.FPrev[APos and WINDOW_MASK] := Self.FHead[H];
  Self.FHead[H] := APos;
end;

function TDeflater.LongestMatch(APos: Int; out ADist: Int): Int;
var
  Cand, Chain, Limit, MaxLen, L, Next: Int;
begin
  Result := 0;
  ADist := 0;
  if APos + MIN_MATCH > Self.FLen then
    Exit;
  MaxLen := Self.FLen - APos;
  if MaxLen > MAX_MATCH then
    MaxLen := MAX_MATCH;
  Limit := APos - WINDOW_SIZE;
  Cand := Self.FHead[Self.HashAt(APos)];
  Chain := Self.FMaxChain;
  while (Cand > Limit) and (Cand >= 0) and (Chain > 0) do
  begin
    { Check the byte that would extend the best match first: most
      candidates fail there. }
    if (Self.FSrc[Cand + Result] = Self.FSrc[APos + Result]) and
       (Self.FSrc[Cand] = Self.FSrc[APos]) then
    begin
      L := 0;
      while (L < MaxLen) and (Self.FSrc[Cand + L] = Self.FSrc[APos + L]) do
        L := L + 1;
      if L > Result then
      begin
        Result := L;
        ADist := APos - Cand;
        if (L >= Self.FNiceLen) or (L >= MaxLen) then
          Break;
      end;
    end;
    Next := Self.FPrev[Cand and WINDOW_MASK];
    if Next >= Cand then
      Break;
    Cand := Next;
    Chain := Chain - 1;
  end;
  if Result < MIN_MATCH then
    Result := 0;
end;

procedure TDeflater.AddSymbol(AVal, ADist: Int);
begin
  Self.FSymVal[Self.FSymCount] := AVal;
  Self.FSymDist[Self.FSymCount] := ADist;
  Self.FSymCount := Self.FSymCount + 1;
  if ADist = 0 then
    Self.FLitFreq[AVal] := Self.FLitFreq[AVal] + 1
  else
  begin
    Self.FLitFreq[257 + Self.FLenCode[AVal]] :=
      Self.FLitFreq[257 + Self.FLenCode[AVal]] + 1;
    Self.FDistFreq[DistSymbol(ADist)] := Self.FDistFreq[DistSymbol(ADist)] + 1;
  end;
end;

procedure TDeflater.WriteStored(AStart, AEnd: Int; AFinal: Boolean);
var
  N, I: Int;
begin
  { At least one block, even for no data (an empty final block). }
  repeat
    N := AEnd - AStart;
    if N > MAX_STORED then
      N := MAX_STORED;
    if AFinal and (AStart + N = AEnd) then
      Self.FW.PutBits(1, 1)
    else
      Self.FW.PutBits(0, 1);
    Self.FW.PutBits(0, 2);
    Self.FW.AlignToByte();
    Self.FW.PutBits(N, 16);
    Self.FW.PutBits(N xor $FFFF, 16);
    for I := AStart to AStart + N - 1 do
      Self.FW.FOut.AppendByte(Byte(Self.FSrc[I]));
    AStart := AStart + N;
  until AStart >= AEnd;
end;

procedure TDeflater.WriteCodes(const ALitLens, ALitCodes, ADistLens,
  ADistCodes: TIntArray);
var
  I, V, D, S: Int;
begin
  for I := 0 to Self.FSymCount - 1 do
  begin
    V := Self.FSymVal[I];
    D := Self.FSymDist[I];
    if D = 0 then
      Self.FW.PutCode(ALitCodes[V], ALitLens[V])
    else
    begin
      S := Self.FLenCode[V];
      Self.FW.PutCode(ALitCodes[257 + S], ALitLens[257 + S]);
      if LENGTH_EXTRA[S] > 0 then
        Self.FW.PutBits(V - LENGTH_BASE[S], LENGTH_EXTRA[S]);
      S := DistSymbol(D);
      Self.FW.PutCode(ADistCodes[S], ADistLens[S]);
      if DIST_EXTRA[S] > 0 then
        Self.FW.PutBits(D - DIST_BASE[S], DIST_EXTRA[S]);
    end;
  end;
  Self.FW.PutCode(ALitCodes[256], ALitLens[256]);
end;

procedure TDeflater.FlushBlock(AEnd: Int; AFinal: Boolean);
var
  FixedLit, FixedDist, FixedLitCodes, FixedDistCodes: TIntArray;
  DynLit, DynDist, DynLitCodes, DynDistCodes: TIntArray;
  AllLens, RleSym, RleExtra, ClFreq, ClLens, ClCodes: TIntArray;
  ExtraBits, FixedBits, DynBits, StoredBits, I, J, Run, NLit, NDist,
    NCl, RleCount, Total: Int;
  Ok: Boolean;
begin
  Self.FLitFreq[256] := 1;

  { Bits the extra fields cost: the same for both Huffman block types. }
  ExtraBits := 0;
  for I := 0 to 28 do
    ExtraBits := ExtraBits + Self.FLitFreq[257 + I] * LENGTH_EXTRA[I];
  for I := 0 to 29 do
    ExtraBits := ExtraBits + Self.FDistFreq[I] * DIST_EXTRA[I];

  { Fixed codes (RFC 1951 3.2.6). }
  SetLength(FixedLit, 288);
  for I := 0 to 143 do FixedLit[I] := 8;
  for I := 144 to 255 do FixedLit[I] := 9;
  for I := 256 to 279 do FixedLit[I] := 7;
  for I := 280 to 287 do FixedLit[I] := 8;
  SetLength(FixedDist, 30);
  for I := 0 to 29 do FixedDist[I] := 5;
  FixedBits := 3 + ExtraBits;
  for I := 0 to 285 do
    FixedBits := FixedBits + Self.FLitFreq[I] * FixedLit[I];
  for I := 0 to 29 do
    FixedBits := FixedBits + Self.FDistFreq[I] * 5;

  { Dynamic codes. }
  BuildLengths(Self.FLitFreq, 286, MAX_BITS, DynLit);
  BuildLengths(Self.FDistFreq, 30, MAX_BITS, DynDist);
  NLit := 286;
  while (NLit > 257) and (DynLit[NLit - 1] = 0) do
    NLit := NLit - 1;
  NDist := 30;
  while (NDist > 1) and (DynDist[NDist - 1] = 0) do
    NDist := NDist - 1;
  { Run-length encode the joined code lengths with symbols 16, 17, 18. }
  Total := NLit + NDist;
  SetLength(AllLens, Total);
  for I := 0 to NLit - 1 do
    AllLens[I] := DynLit[I];
  for I := 0 to NDist - 1 do
    AllLens[NLit + I] := DynDist[I];
  SetLength(RleSym, Total);
  SetLength(RleExtra, Total);
  SetLength(ClFreq, 19);
  for I := 0 to 18 do
    ClFreq[I] := 0;
  RleCount := 0;
  I := 0;
  while I < Total do
  begin
    Run := 1;
    while (I + Run < Total) and (AllLens[I + Run] = AllLens[I]) do
      Run := Run + 1;
    if (AllLens[I] = 0) and (Run >= 3) then
    begin
      if Run > 138 then
        Run := 138;
      if Run >= 11 then
      begin
        RleSym[RleCount] := 18;
        RleExtra[RleCount] := Run - 11;
      end
      else
      begin
        RleSym[RleCount] := 17;
        RleExtra[RleCount] := Run - 3;
      end;
      RleCount := RleCount + 1;
      I := I + Run;
    end
    else if (AllLens[I] <> 0) and (Run >= 4) then
    begin
      { The length itself, then repeats of it. }
      RleSym[RleCount] := AllLens[I];
      RleExtra[RleCount] := 0;
      RleCount := RleCount + 1;
      Run := Run - 1;
      if Run > 6 then
        Run := 6;
      RleSym[RleCount] := 16;
      RleExtra[RleCount] := Run - 3;
      RleCount := RleCount + 1;
      I := I + 1 + Run;
    end
    else
    begin
      RleSym[RleCount] := AllLens[I];
      RleExtra[RleCount] := 0;
      RleCount := RleCount + 1;
      I := I + 1;
    end;
  end;
  for I := 0 to RleCount - 1 do
    ClFreq[RleSym[I]] := ClFreq[RleSym[I]] + 1;
  BuildLengths(ClFreq, 19, 7, ClLens);
  NCl := 19;
  while (NCl > 4) and (ClLens[CLEN_ORDER[NCl - 1]] = 0) do
    NCl := NCl - 1;

  DynBits := 3 + 5 + 5 + 4 + NCl * 3 + ExtraBits;
  for I := 0 to RleCount - 1 do
  begin
    DynBits := DynBits + ClLens[RleSym[I]];
    if RleSym[I] = 16 then
      DynBits := DynBits + 2
    else if RleSym[I] = 17 then
      DynBits := DynBits + 3
    else if RleSym[I] = 18 then
      DynBits := DynBits + 7;
  end;
  for I := 0 to 285 do
    DynBits := DynBits + Self.FLitFreq[I] * DynLit[I];
  for I := 0 to 29 do
    DynBits := DynBits + Self.FDistFreq[I] * DynDist[I];

  { A stored block: header, alignment (at most 7 bits), LEN and NLEN, per
    64 KiB piece. }
  StoredBits := (AEnd - Self.FBlockStart) * 8 +
    ((AEnd - Self.FBlockStart) div MAX_STORED + 1) * 40;

  if (StoredBits <= FixedBits) and (StoredBits <= DynBits) then
    Self.WriteStored(Self.FBlockStart, AEnd, AFinal)
  else
  begin
    if AFinal then
      Self.FW.PutBits(1, 1)
    else
      Self.FW.PutBits(0, 1);
    if FixedBits <= DynBits then
    begin
      Self.FW.PutBits(1, 2);
      Ok := CanonicalCodes(FixedLit, 288, FixedLitCodes) and
        CanonicalCodes(FixedDist, 30, FixedDistCodes);
      Self.WriteCodes(FixedLit, FixedLitCodes, FixedDist, FixedDistCodes);
    end
    else
    begin
      Self.FW.PutBits(2, 2);
      Self.FW.PutBits(NLit - 257, 5);
      Self.FW.PutBits(NDist - 1, 5);
      Self.FW.PutBits(NCl - 4, 4);
      for I := 0 to NCl - 1 do
        Self.FW.PutBits(ClLens[CLEN_ORDER[I]], 3);
      Ok := CanonicalCodes(ClLens, 19, ClCodes) and
        CanonicalCodes(DynLit, 286, DynLitCodes) and
        CanonicalCodes(DynDist, 30, DynDistCodes);
      for J := 0 to RleCount - 1 do
      begin
        Self.FW.PutCode(ClCodes[RleSym[J]], ClLens[RleSym[J]]);
        if RleSym[J] = 16 then
          Self.FW.PutBits(RleExtra[J], 2)
        else if RleSym[J] = 17 then
          Self.FW.PutBits(RleExtra[J], 3)
        else if RleSym[J] = 18 then
          Self.FW.PutBits(RleExtra[J], 7);
      end;
      Self.WriteCodes(DynLit, DynLitCodes, DynDist, DynDistCodes);
    end;
    if not Ok then
      raise ECompressionError.Create('Deflate: internal error building codes');
  end;

  Self.FSymCount := 0;
  Self.FBlockStart := AEnd;
  for I := 0 to 285 do
    Self.FLitFreq[I] := 0;
  for I := 0 to 29 do
    Self.FDistFreq[I] := 0;
end;

function TDeflater.Compress: string;
var
  Pos, Len, Dist, I: Int;
begin
  Pos := 0;
  while Pos < Self.FLen do
  begin
    Len := Self.LongestMatch(Pos, Dist);
    if Len >= MIN_MATCH then
    begin
      Self.AddSymbol(Len, Dist);
      for I := 0 to Len - 1 do
        Self.Insert(Pos + I);
      Pos := Pos + Len;
    end
    else
    begin
      Self.AddSymbol(Byte(Self.FSrc[Pos]), 0);
      Self.Insert(Pos);
      Pos := Pos + 1;
    end;
    if Self.FSymCount = BLOCK_SYMBOLS then
      Self.FlushBlock(Pos, Pos >= Self.FLen);
  end;
  if (Self.FSymCount > 0) or (Self.FLen = 0) then
    Self.FlushBlock(Self.FLen, True);
  Result := Self.FW.Finish();
end;

function StoreOnly(const AData: string): string;
var
  W: TBitWriter;
  Pos, N, I: Int;
begin
  W := TBitWriter.Create();
  try
    Pos := 0;
    repeat
      N := Length(AData) - Pos;
      if N > MAX_STORED then
        N := MAX_STORED;
      if Pos + N = Length(AData) then
        W.PutBits(1, 3)
      else
        W.PutBits(0, 3);
      W.AlignToByte();
      W.PutBits(N, 16);
      W.PutBits(N xor $FFFF, 16);
      for I := Pos to Pos + N - 1 do
        W.FOut.AppendByte(Byte(AData[I]));
      Pos := Pos + N;
    until Pos >= Length(AData);
    Result := W.Finish();
  finally
    W.Free();
  end;
end;

function Deflate(const AData: string; ALevel: Int): string;
var
  D: TDeflater;
begin
  if ALevel <= 0 then
    Exit(StoreOnly(AData));
  if ALevel > 9 then
    ALevel := 9;
  D := TDeflater.Create(AData, ALevel);
  try
    Result := D.Compress();
  finally
    D.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ zlib (RFC 1950)                                                     }
{ ------------------------------------------------------------------ }

function ZlibCompress(const AData: string; ALevel: Int): string;
var
  SB: TStringBuilder;
  Flg: Int;
  Adler: UInt32;
begin
  { CMF $78: deflate with a 32 KiB window.  FLEVEL is informative only. }
  if ALevel <= 1 then
    Flg := 0
  else if ALevel <= 5 then
    Flg := 1 shl 6
  else if ALevel = 6 then
    Flg := 2 shl 6
  else
    Flg := 3 shl 6;
  Flg := Flg + (31 - (($78 * 256 + Flg) mod 31));
  Adler := Adler32(AData);
  SB := TStringBuilder.Create();
  SB.AppendByte($78);
  SB.AppendByte(Flg);
  SB.Append(Deflate(AData, ALevel));
  SB.AppendByte((Adler shr 24) and $FF);
  SB.AppendByte((Adler shr 16) and $FF);
  SB.AppendByte((Adler shr 8) and $FF);
  SB.AppendByte(Adler and $FF);
  Result := SB.ToString();
  SB.Free();
end;

function ZlibDecompress(const AData: string): string;
var
  Cmf, Flg, EndPos, I: Int;
  Expected: UInt32;
begin
  if Length(AData) < 6 then
    raise ECompressionError.Create('Invalid zlib data: too short');
  Cmf := Byte(AData[0]);
  Flg := Byte(AData[1]);
  if ((Cmf and $0F) <> 8) or ((Cmf shr 4) > 7) then
    raise ECompressionError.Create('Invalid zlib data: not a deflate stream');
  if (Cmf * 256 + Flg) mod 31 <> 0 then
    raise ECompressionError.Create('Invalid zlib data: header check failed');
  if (Flg and $20) <> 0 then
    raise ECompressionError.Create(
      'Unsupported zlib data: a preset dictionary is required');
  Result := InflateAt(AData, 2, EndPos);
  if EndPos + 4 > Length(AData) then
    raise ECompressionError.Create('Invalid zlib data: missing Adler-32');
  Expected := 0;
  for I := 0 to 3 do
    Expected := (Expected shl 8) or Byte(AData[EndPos + I]);
  if Expected <> Adler32(Result) then
    raise ECompressionError.Create('Invalid zlib data: Adler-32 mismatch');
end;

end.
