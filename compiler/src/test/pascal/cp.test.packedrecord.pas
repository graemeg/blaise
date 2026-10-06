{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.packedrecord;

{ Tests for the `packed record` qualifier.

  Coverage:
    - `packed` reserved word lexes to tkPacked.
    - `packed record ... end` parses into a TRecordTypeDef with IsPacked=True.
    - In a packed record, fields are laid out at the next byte (no alignment
      padding) and the record itself has no tail padding.
    - The non-packed form is unaffected.
    - ARC-managed fields (string / class / interface) still require 8-byte
      storage alignment; the field offset is forced to the next 8-byte
      boundary regardless of `packed`.
    - Record-level alignment (MaxAlign) drops to 1 for packed records, so
      arrays of packed records pack tight too.
    - `packed` is only legal in front of `record`; `packed class` / `packed
      array` produce a parse error. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TPackedRecordTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestLexer_Packed_Keyword;
    procedure TestParse_PackedRecord_SetsIsPacked;
    procedure TestParse_PlainRecord_IsPackedFalse;
    procedure TestSemantic_PackedRecord_TypeDescIsPacked;
    procedure TestSemantic_PackedRecord_ByteThenInt_NoAlignPadding;
    procedure TestSemantic_PackedRecord_TotalSize_NoTailPad;
    procedure TestSemantic_PackedRecord_MaxAlign_Is1;
    procedure TestSemantic_PackedRecord_StringField_StaysAlignedTo8;
    procedure TestParse_PackedClass_RaisesError;
    procedure TestParse_PackedArray_RaisesError;
    procedure TestParse_PackedArray_ErrorMentionsSetOf;
    procedure TestParse_BitpackedArray_RaisesError;
    procedure TestParse_Bitpacked_ErrorMentionsSetOf;
  end;

  [Threaded]
  TPackedRecordE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_PackedRecord_SizeHasNoPadding;
    procedure TestRun_PackedRecord_ByteInt_Offsets;
    procedure TestRun_PackedRecord_SizeOfMatchesPacked;
  end;

implementation

function TPackedRecordTests.AnalyseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

procedure TPackedRecordTests.TestLexer_Packed_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('packed');
  try
    T := L.Next();
    AssertEquals('packed maps to tkPacked', Ord(tkPacked), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

procedure TPackedRecordTests.TestParse_PackedRecord_SetsIsPacked;
const
  Src = '''
        program P;
        type
          TFoo = packed record
            A: Byte;
            B: Integer;
          end;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  RD:   TRecordTypeDef;
begin
  Prog := AnalyseSrc(Src);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    AssertTrue('is TRecordTypeDef', TD.Def is TRecordTypeDef);
    RD := TRecordTypeDef(TD.Def);
    AssertTrue('IsPacked = True', RD.IsPacked);
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestParse_PlainRecord_IsPackedFalse;
const
  Src = '''
        program P;
        type TFoo = record A: Integer; end;
        begin end.
        ''';
var
  Prog: TProgram;
  RD:   TRecordTypeDef;
begin
  Prog := AnalyseSrc(Src);
  try
    RD := TRecordTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertFalse('IsPacked = False on plain record', RD.IsPacked);
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestSemantic_PackedRecord_TypeDescIsPacked;
const
  Src = '''
        program P;
        type TFoo = packed record A: Integer; end;
        var R: TFoo;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertTrue('IsPacked propagated to TRecordTypeDesc', RT.IsPacked);
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestSemantic_PackedRecord_ByteThenInt_NoAlignPadding;
const
  Src = '''
        program P;
        type TFoo = packed record
          A: Byte;
          B: Integer;
        end;
        var R: TFoo;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FldA, FldB: TFieldInfo;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    FldA := RT.FindField('A');
    FldB := RT.FindField('B');
    AssertEquals('A offset', 0, FldA.Offset);
    AssertEquals('B offset (no align padding)', 1, FldB.Offset);
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestSemantic_PackedRecord_TotalSize_NoTailPad;
const
  Src = '''
        program P;
        type TFoo = packed record
          A: Byte;
          B: Integer;
        end;
        var R: TFoo;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('TotalSize = 1 + 4 = 5 (no tail pad)', 5, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestSemantic_PackedRecord_MaxAlign_Is1;
const
  Src = '''
        program P;
        type TFoo = packed record
          A: Byte;
          B: Int64;
        end;
        var R: TFoo;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('MaxAlign = 1 for packed', 1, RT.MaxAlign());
    AssertEquals('B offset = 1 (no 8-byte align)', 1,
                 RT.FindField('B').Offset);
    AssertEquals('TotalSize = 9 (no tail pad)', 9, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestSemantic_PackedRecord_StringField_StaysAlignedTo8;
const
  { String fields are ARC-managed pointers — _StringRelease does a 64-bit load
    so they must remain 8-byte aligned even inside a packed record. }
  Src = '''
        program P;
        type TFoo = packed record
          A: Byte;
          S: string;
        end;
        var R: TFoo;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('A at 0',      0, RT.FindField('A').Offset);
    AssertEquals('S aligned to 8', 8, RT.FindField('S').Offset);
  finally
    Prog.Free();
  end;
end;

procedure TPackedRecordTests.TestParse_PackedClass_RaisesError;
const
  Src = '''
        program P;
        type TFoo = packed class A: Integer; end;
        begin end.
        ''';
var
  L: TLexer;
  P: TParser;
  Prog: TProgram;
  Raised: Boolean;
begin
  Raised := False;
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    try
      Prog := P.Parse();
      Prog.Free();
    except
      on EParseError do Raised := True;
    end;
  finally
    P.Free();
    L.Free();
  end;
  AssertTrue('packed class rejected', Raised);
end;

procedure TPackedRecordTests.TestParse_PackedArray_RaisesError;
const
  Src = '''
        program P;
        type TArr = packed array[0..3] of Byte;
        begin end.
        ''';
var
  L: TLexer;
  P: TParser;
  Prog: TProgram;
  Raised: Boolean;
begin
  Raised := False;
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    try
      Prog := P.Parse();
      Prog.Free();
    except
      on EParseError do Raised := True;
    end;
  finally
    P.Free();
    L.Free();
  end;
  AssertTrue('packed array rejected', Raised);
end;

procedure TPackedRecordTests.TestParse_PackedArray_ErrorMentionsSetOf;
const
  Src = '''
        program P;
        type TArr = packed array[0..3] of Byte;
        begin end.
        ''';
var
  L: TLexer;
  P: TParser;
  Prog: TProgram;
  Msg: string;
begin
  Msg := '';
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    try
      Prog := P.Parse();
      Prog.Free();
    except
      on E: EParseError do Msg := E.Message;
    end;
  finally
    P.Free();
    L.Free();
  end;
  AssertTrue('error names packed array', Pos('packed array', Msg) >= 0);
  AssertTrue('error suggests set of', Pos('set of', Msg) >= 0);
end;

procedure TPackedRecordTests.TestParse_BitpackedArray_RaisesError;
const
  Src = '''
        program P;
        type TArr = bitpacked array[0..2] of Boolean;
        begin end.
        ''';
var
  L: TLexer;
  P: TParser;
  Prog: TProgram;
  Raised: Boolean;
begin
  Raised := False;
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    try
      Prog := P.Parse();
      Prog.Free();
    except
      on EParseError do Raised := True;
    end;
  finally
    P.Free();
    L.Free();
  end;
  AssertTrue('bitpacked array rejected', Raised);
end;

procedure TPackedRecordTests.TestParse_Bitpacked_ErrorMentionsSetOf;
const
  Src = '''
        program P;
        type TArr = bitpacked array[0..2] of Boolean;
        begin end.
        ''';
var
  L: TLexer;
  P: TParser;
  Prog: TProgram;
  Msg: string;
begin
  Msg := '';
  L := TLexer.Create(Src);
  P := TParser.Create(L);
  try
    try
      Prog := P.Parse();
      Prog.Free();
    except
      on E: EParseError do Msg := E.Message;
    end;
  finally
    P.Free();
    L.Free();
  end;
  AssertTrue('error names bitpacked', Pos('bitpacked', Msg) >= 0);
  AssertTrue('error suggests set of', Pos('set of', Msg) >= 0);
end;

procedure TPackedRecordE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-packed-record');
end;

const
  LE = #10;

  SrcByteIntOffsets = '''
    program P;
    type TFoo = packed record
      A: Byte;
      B: Integer;
    end;
    var R: TFoo;
    begin
      R.A := 9;
      R.B := 12345;
      WriteLn(R.A);
      WriteLn(R.B);
      WriteLn(SizeOf(TFoo))
    end.
    ''';

  SrcPackedVsUnpacked = '''
    program P;
    type
      TPlain  =        record A: Byte; B: Int64; end;
      TPacked = packed record A: Byte; B: Int64; end;
    begin
      WriteLn(SizeOf(TPlain));
      WriteLn(SizeOf(TPacked))
    end.
    ''';

procedure TPackedRecordE2ETests.TestRun_PackedRecord_ByteInt_Offsets;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcByteIntOffsets, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('A=9, B=12345, SizeOf=5',
    '9' + LE + '12345' + LE + '5' + LE, Output);
end;

procedure TPackedRecordE2ETests.TestRun_PackedRecord_SizeOfMatchesPacked;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcPackedVsUnpacked, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { Plain: A at 0, B at 8 (8-byte aligned), tail pad to MaxAlign=8 → 16.
    Packed: A at 0, B at 1, no tail pad → 9. }
  AssertEquals('plain=16, packed=9',
    '16' + LE + '9' + LE, Output);
end;

procedure TPackedRecordE2ETests.TestRun_PackedRecord_SizeHasNoPadding;
const
  {
    A packed record has no padding: Byte + Integer is 5 bytes, against 8 for
    the unpacked record.  Replaces the QBE IR check in cp.test.packedrecord. }
  Src = '''
    program P;
    type
      TPk = packed record
        A: Byte;
        B: Integer;
      end;
      TUnpk = record
        A: Byte;
        B: Integer;
      end;
    begin
      WriteLn(SizeOf(TPk), ' ', SizeOf(TUnpk))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '5 8' + LE, 0);
end;

initialization
  RegisterTest(TPackedRecordTests);
  RegisterTest(TPackedRecordE2ETests);

end.
