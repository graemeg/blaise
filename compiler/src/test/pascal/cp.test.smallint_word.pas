{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.smallint_word;

{ Tests for the 16-bit integer types SmallInt (signed) and Word (unsigned),
  plus their Delphi-style aliases Int16 and UInt16.

  Coverage:
    - All four names resolve, SmallInt/Int16 and Word/UInt16 share descriptors.
    - SizeOf is 2 for every name.
    - Fields are packed at 2-byte stride; mixed records align correctly.
    - Load/store use loadsh/loaduh/storeh (16-bit half-word ops).
    - Integer/UInt32 widen implicitly in expressions.
    - WriteLn and IntToStr handle both signed and unsigned values. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TSmallIntWordTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    procedure TestSemantic_SmallInt_TypeRegistered;
    procedure TestSemantic_Word_TypeRegistered;
    procedure TestSemantic_Int16_AliasOfSmallInt;
    procedure TestSemantic_UInt16_AliasOfWord;
    procedure TestSemantic_SizeOf_SmallInt_Is2;
    procedure TestSemantic_SizeOf_Word_Is2;
    procedure TestSemantic_SmallIntField_RecordPacks;
    procedure TestSemantic_MixedRecord_AlignsTo16;
    procedure TestCodegen_SmallIntField_UsesLoadsh;
    procedure TestCodegen_WordField_UsesLoaduh;
    procedure TestCodegen_SmallIntField_UsesStoreh;
    { BUG-20260728-qbe-narrow-var-load: a plain VARIABLE of a narrow type must
      be read with the load matching its STORAGE width, not a blanket loadw.
      A var/out callee writes it with storeh/storeb, so a 32-bit read returns
      the untouched upper bytes. }
    procedure TestCodegen_SmallIntVar_UsesLoadsh_NotLoadw;
    procedure TestCodegen_WordVar_UsesLoaduh_NotLoadw;
    procedure TestCodegen_ByteVar_UsesLoadub_NotLoadw;
  end;

  [Threaded]
  TSmallIntWordE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_SmallInt_RoundTrip;
    procedure TestRun_Word_RoundTrip;
    procedure TestRun_SmallInt_Negative;
    procedure TestRun_Word_MaxValue;
    procedure TestRun_MixedRecord_RoundTrip;
    procedure TestRun_ImplicitSelf_ByteFields_NoBleed;
    procedure TestRun_ImplicitSelf_SmallIntWord_Fields;
    { BUG-20260728-qbe-narrow-var-load — the behaviour the IR tests above pin.
      A var/out param of a narrow SIGNED type read back as its unsigned
      bit-pattern (-300 -> 65236), and the sign test flipped with it, so the
      corruption changed control flow rather than merely printing oddly. }
    procedure TestRun_VarParam_SmallInt_SignPreserved;
    procedure TestRun_OutParam_SmallInt_SignPreserved;
    procedure TestRun_VarParam_NarrowWidths_RoundTrip;
  end;

implementation

function TSmallIntWordTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TSmallIntWordTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_SmallInt_TypeRegistered;
const
  Src = '''
        program P;
        var X: SmallInt;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('resolves',           T <> nil);
    AssertEquals('Kind = tySmallInt', Ord(tySmallInt), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_Word_TypeRegistered;
const
  Src = '''
        program P;
        var X: Word;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('resolves',       T <> nil);
    AssertEquals('Kind = tyWord', Ord(tyWord), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_Int16_AliasOfSmallInt;
const
  Src = '''
        program P;
        var A: SmallInt;
        var B: Int16;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertSame('SmallInt and Int16 share descriptor',
      TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType,
      TVarDecl(Prog.Block.Decls.Items[1]).ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_UInt16_AliasOfWord;
const
  Src = '''
        program P;
        var A: Word;
        var B: UInt16;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertSame('Word and UInt16 share descriptor',
      TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType,
      TVarDecl(Prog.Block.Decls.Items[1]).ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_SizeOf_SmallInt_Is2;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin N := SizeOf(SmallInt) end.
        ''');
  AssertTrue('SizeOf(SmallInt) is 2', Pos('copy 2', IR) > 0);
end;

procedure TSmallIntWordTests.TestSemantic_SizeOf_Word_Is2;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin N := SizeOf(Word) end.
        ''');
  AssertTrue('SizeOf(Word) is 2', Pos('copy 2', IR) > 0);
end;

procedure TSmallIntWordTests.TestSemantic_SmallIntField_RecordPacks;
const
  Src = '''
        program P;
        type
          TFour = record
            A: SmallInt;
            B: SmallInt;
            C: SmallInt;
            D: SmallInt;
          end;
        var R: TFour;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('A at 0', 0, RT.FindField('A').Offset);
    AssertEquals('B at 2', 2, RT.FindField('B').Offset);
    AssertEquals('C at 4', 4, RT.FindField('C').Offset);
    AssertEquals('D at 6', 6, RT.FindField('D').Offset);
    AssertEquals('total 8', 8, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestSemantic_MixedRecord_AlignsTo16;
const
  { Byte + SmallInt + Integer = 1 + (pad 1) + 2 + 4 = 8 bytes. }
  Src = '''
        program P;
        type
          TMixed = record
            Tag: Byte;
            ID:  SmallInt;
            Val: Integer;
          end;
        var R: TMixed;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('Tag at 0', 0, RT.FindField('Tag').Offset);
    AssertEquals('ID at 2 (after 1-byte pad)', 2, RT.FindField('ID').Offset);
    AssertEquals('Val at 4', 4, RT.FindField('Val').Offset);
    AssertEquals('total 8',  8, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TSmallIntWordTests.TestCodegen_SmallIntField_UsesLoadsh;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record V: SmallInt; end;
        var R: TR;
        var X: Integer;
        begin X := R.V end.
        ''');
  AssertTrue('SmallInt field load uses loadsh', Pos('loadsh', IR) > 0);
end;

procedure TSmallIntWordTests.TestCodegen_WordField_UsesLoaduh;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record V: Word; end;
        var R: TR;
        var X: Integer;
        begin X := R.V end.
        ''');
  AssertTrue('Word field load uses loaduh', Pos('loaduh', IR) > 0);
end;

procedure TSmallIntWordTests.TestCodegen_SmallIntField_UsesStoreh;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TR = record V: SmallInt; end;
        var R: TR;
        begin R.V := 42 end.
        ''');
  AssertTrue('SmallInt field store uses storeh', Pos('storeh', IR) > 0);
end;

{ BUG-20260728-qbe-narrow-var-load.

  A record FIELD of a narrow type was already read at its own width (the three
  tests above), but a plain VARIABLE was not: the scalar-identifier arm of
  EmitExpr switched on QbeTypeOf, which collapses tyByte/tySmallInt/tyWord/
  tyBoolean all onto 'w', and then emitted a blanket loadw.

  Reading 4 bytes from 2-byte storage is only observable once something has
  written FEWER than 4 bytes to it, which is exactly what a var/out callee
  does — it stores through the caller's address at the declared width
  (storeh/storeb).  A direct local assignment stores full width, so the plain
  case masked the bug, and it surfaced only across a var/out call.

  These three assert the load instruction directly, so a regression is pinned
  at the IR rather than only as wrong output. }
procedure TSmallIntWordTests.TestCodegen_SmallIntVar_UsesLoadsh_NotLoadw;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        procedure SetIt(var X: SmallInt);
        begin X := -300 end;
        var S: SmallInt;
        var L: Int64;
        begin SetIt(S); L := S; WriteLn(L) end.
        ''');
  AssertTrue('SmallInt variable load uses loadsh (sign-extending)',
    Pos('loadsh', IR) > 0);
  AssertTrue('SmallInt variable is never read with a 32-bit loadw — '
    + 'the callee wrote only 2 bytes, so the upper half is stale',
    Pos('loadw $S', IR) < 0);
end;

procedure TSmallIntWordTests.TestCodegen_WordVar_UsesLoaduh_NotLoadw;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        procedure SetIt(var X: Word);
        begin X := 60000 end;
        var W: Word;
        var L: Int64;
        begin SetIt(W); L := W; WriteLn(L) end.
        ''');
  AssertTrue('Word variable load uses loaduh (zero-extending)',
    Pos('loaduh', IR) > 0);
  AssertTrue('Word variable is never read with a 32-bit loadw',
    Pos('loadw $W', IR) < 0);
end;

procedure TSmallIntWordTests.TestCodegen_ByteVar_UsesLoadub_NotLoadw;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        procedure SetIt(var X: Byte);
        begin X := 200 end;
        var B: Byte;
        var L: Int64;
        begin SetIt(B); L := B; WriteLn(L) end.
        ''');
  AssertTrue('Byte variable load uses loadub', Pos('loadub', IR) > 0);
  AssertTrue('Byte variable is never read with a 32-bit loadw',
    Pos('loadw $B', IR) < 0);
end;

{ ---------- e2e ---------- }

procedure TSmallIntWordE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-smallint-word');
end;

const
  LE = #10;

  SrcSmallIntRoundTrip = '''
    program P;
    var X: SmallInt;
    begin
      X := 12345;
      WriteLn(X)
    end.
    ''';

  SrcWordRoundTrip = '''
    program P;
    var X: Word;
    begin
      X := 60000;
      WriteLn(X)
    end.
    ''';

  SrcSmallIntNegative = '''
    program P;
    var X: SmallInt;
    begin
      X := -1;
      WriteLn(X)
    end.
    ''';

  SrcWordMax = '''
    program P;
    var X: Word;
    begin
      X := 65535;
      WriteLn(X)
    end.
    ''';

  SrcImplicitSelfByteFields = '''
    program P;
    type
      TFoo = class
        A: Byte;
        B: Byte;
        C: Byte;
        D: Byte;
        procedure SetAll;
        procedure Show;
      end;
    procedure TFoo.SetAll;
    begin
      A := 1; B := 2; C := 3; D := 4;
    end;
    procedure TFoo.Show;
    begin
      WriteLn(A); WriteLn(B); WriteLn(C); WriteLn(D);
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.SetAll();
      F.Show();
      F.Free()
    end.
    ''';

  SrcImplicitSelfSmallIntFields = '''
    program P;
    type
      TFoo = class
        A: SmallInt;
        B: Word;
        procedure SetAll;
        procedure Show;
      end;
    procedure TFoo.SetAll;
    begin
      A := -1000;
      B := 60000;
    end;
    procedure TFoo.Show;
    begin
      WriteLn(A);
      WriteLn(B);
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.SetAll();
      F.Show();
      F.Free()
    end.
    ''';

  { BUG-20260728-qbe-narrow-var-load — see the IR tests for the mechanism.
    The sign test is included deliberately: the corruption did not merely
    print oddly, it made `S < 0` evaluate False for a negative value, so it
    changed control flow. }
  SrcVarParamSmallInt = '''
    program P;
    procedure SetIt(var X: SmallInt);
    begin
      X := -300
    end;
    var S: SmallInt;
    var L: Int64;
    begin
      SetIt(S);
      WriteLn(S);
      WriteLn(S < 0);
      L := S;
      WriteLn(L)
    end.
    ''';

  SrcOutParamSmallInt = '''
    program P;
    procedure SetIt(out X: SmallInt);
    begin
      X := -300
    end;
    var S: SmallInt;
    var L: Int64;
    begin
      SetIt(S);
      WriteLn(S);
      WriteLn(S < 0);
      L := S;
      WriteLn(L)
    end.
    ''';

  { All four narrow widths across a var call, signed and unsigned, each also
    widened to Int64 — widening is what exposed the stale upper bytes. }
  SrcVarParamNarrowWidths = '''
    program P;
    procedure SetB(var X: Byte);
    begin X := 200 end;
    procedure SetW(var X: Word);
    begin X := 60000 end;
    procedure SetS(var X: SmallInt);
    begin X := -300 end;
    procedure SetI(var X: Integer);
    begin X := -8 end;
    var B: Byte;
    var W: Word;
    var S: SmallInt;
    var I: Integer;
    var L: Int64;
    begin
      SetB(B); L := B; WriteLn(L);
      SetW(W); L := W; WriteLn(L);
      SetS(S); L := S; WriteLn(L);
      SetI(I); L := I; WriteLn(L)
    end.
    ''';

  SrcMixedRecord = '''
    program P;
    type
      TMixed = record
        Tag: Byte;
        ID:  SmallInt;
        Val: Integer;
      end;
    var R: TMixed;
    begin
      R.Tag := 9;
      R.ID  := -100;
      R.Val := 12345;
      WriteLn(R.Tag);
      WriteLn(R.ID);
      WriteLn(R.Val);
      WriteLn(SizeOf(TMixed))
    end.
    ''';

procedure TSmallIntWordE2ETests.TestRun_SmallInt_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSmallIntRoundTrip, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('12345', '12345' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_Word_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWordRoundTrip, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('60000', '60000' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_SmallInt_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSmallIntNegative, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('-1 sign-extended', '-1' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_Word_MaxValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWordMax, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('65535 zero-extended', '65535' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_MixedRecord_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMixedRecord, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Tag, ID, Val, SizeOf',
    '9' + LE + '-100' + LE + '12345' + LE + '8' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_ImplicitSelf_ByteFields_NoBleed;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcImplicitSelfByteFields, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('per-field bytes, no over-write bleed',
    '1' + LE + '2' + LE + '3' + LE + '4' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_ImplicitSelf_SmallIntWord_Fields;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcImplicitSelfSmallIntFields, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('SmallInt sign-extend + Word zero-extend',
    '-1000' + LE + '60000' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_VarParam_SmallInt_SignPreserved;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamSmallInt, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { pre-fix (qbe): 65236 / False / 65236 — the callee stored 2 bytes with
    storeh and the read took a 32-bit loadw, so the sign was lost with the
    stale upper half }
  AssertEquals('negative SmallInt survives a var call, sign test included',
    '-300' + LE + 'True' + LE + '-300' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_OutParam_SmallInt_SignPreserved;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOutParamSmallInt, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('out behaves exactly as var here',
    '-300' + LE + 'True' + LE + '-300' + LE, Output);
end;

procedure TSmallIntWordE2ETests.TestRun_VarParam_NarrowWidths_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamNarrowWidths, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('every narrow width round-trips through a var param',
    '200' + LE + '60000' + LE + '-300' + LE + '-8' + LE, Output);
end;

initialization
  RegisterTest(TSmallIntWordTests);
  RegisterTest(TSmallIntWordE2ETests);

end.
