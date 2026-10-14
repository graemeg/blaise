{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.threadvar;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, cp.test.harness;

type
  TThreadVarTests = class(TTestCase)
  private
    function GenerateNativeAsm(const ASrc: string): string;
  published
    procedure TestParser_ThreadVarBlockParsed;
    procedure TestParser_ThreadVarIsGlobal;
    procedure TestSemantic_ThreadVarMustBeGlobalScope;
    procedure TestCodegen_ThreadVars_InThreadLocalStorage;
    { @ThreadVar must yield the PER-THREAD address (%fs:0 + @tpoff), not
      the static leaq Name(%rip).  A static address makes every thread's
      @TV identical — which silently broke the allocator's MyTid identity
      (runtime.mem) and any code holding a pointer into a threadvar. }
    procedure TestCodegenNative_AddrOfThreadVar_UsesTls;
    procedure TestCodegenNative_AddrOfPlainGlobal_StaysRipRelative;
    { an unmanaged RECORD threadvar: per-thread storage (Mach-O TLV / ELF
      @tpoff) addressed for a field store.  arm64 refused the type. }
    procedure TestCodegen_RecordThreadVar_FieldStoreThroughTls;
    { x86-64: every lowering that names a threadvar goes through its TLS
      address.  SetLength / Delete / Free / sret results wrote the static
      Name(%rip) -- the TLS template, not the thread's copy. }
    procedure TestCodegenX86_ThreadVarUpdates_NeverRipRelative;
    { lea ignores a segment override: leaq %fs:X@tpoff yields the bare
      offset, so an address-of path must never emit it (a closure threadvar
      call jumped through that offset) }
    procedure TestCodegenX86_ThreadVarAddress_NeverLeaqThroughSegment;
    { .tbss lays each threadvar out like the plain global of its type: the
      interface obj+itab pair under its _obj / _itab labels, a closure's
      16-byte Code+Env pair }
    procedure TestCodegenX86_ThreadVarTbssLayout_MatchesPlainGlobals;
    { arm64: a threadvar of every type is a Mach-O TLV whose storage is sized
      like the plain global (it refused all but scalars, strings, classes and
      unmanaged aggregates), and never also an ordinary _g_ global }
    procedure TestCodegenArm64_ThreadVarStorage_SizedLikePlainGlobals;
    { an interface threadvar is ONE 16-byte TLV; its itab half is reached at
      the TLV address + 8, keeping the pair contiguous for a var argument }
    procedure TestCodegenArm64_IntfThreadVar_ItabAtTlvPlus8;
  end;

implementation

function TThreadVarTests.GenerateNativeAsm(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenNative;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Pr := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Pr);
    finally
      A.Free();
    end;
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(LinuxX64Target());
      CG.Generate(Pr);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Pr.Free();
  end;
end;

procedure TThreadVarTests.TestParser_ThreadVarBlockParsed;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  D:  TVarDecl;
begin
  L  := TLexer.Create(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  X: Integer;' + #10 +
    'begin' + #10 +
    'end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  try
    AssertEquals(1, Pr.Block.Decls.Count);
    D := TVarDecl(Pr.Block.Decls.Items[0]);
    AssertEquals('X', D.Names.Strings[0]);
    AssertTrue(D.IsThreadVar);
  finally
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TThreadVarTests.TestParser_ThreadVarIsGlobal;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  D:  TVarDecl;
begin
  L  := TLexer.Create(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  Y: Int64;' + #10 +
    'begin' + #10 +
    'end.');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    D := TVarDecl(Pr.Block.Decls.Items[0]);
    AssertTrue(D.IsGlobal);
    AssertTrue(D.IsThreadVar);
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

procedure TThreadVarTests.TestSemantic_ThreadVarMustBeGlobalScope;
begin
  try
    Analyse(
      'program P;' + #10 +
      'procedure Foo;' + #10 +
      'threadvar' + #10 +
      '  Z: Integer;' + #10 +
      'begin end;' + #10 +
      'begin' + #10 +
      'end.').Free();
    Fail('Expected EParseError for threadvar inside procedure');
  except
    on E: EParseError do ;
  end;
end;

procedure TThreadVarTests.TestCodegen_ThreadVars_InThreadLocalStorage;
const
  Src = '''
    program P;
    var
      A: Integer;
    threadvar
      Counter: Integer;
      Name: String;
      Ptr: Pointer;
      Buckets: array[0..7] of Pointer;
    begin
      A := 1; Counter := 42; Name := 'hello'; Ptr := nil; Buckets[0] := nil
    end.
    ''';
var
  X86, A64: string;
  Tbss: Integer;
begin
  { threadvars live in thread-local storage at their full size; an
    ordinary global stays in ordinary data.  Per-thread isolation itself is
    run by TE2EThreadingTests; this pins where the storage is placed. }
  X86 := GenAsm(Src, TargetX86_64);
  Tbss := Pos('.section .tbss', X86);
  AssertTrue('x86-64: a .tbss section', Tbss >= 0);
  AssertTrue('x86-64: Counter in .tbss', Pos(#10 + 'Counter:', X86) > Tbss);
  AssertTrue('x86-64: Name in .tbss', Pos(#10 + 'Name:', X86) > Tbss);
  AssertTrue('x86-64: Ptr in .tbss', Pos(#10 + 'Ptr:', X86) > Tbss);
  AssertTrue('x86-64: Buckets is 64 bytes',
    Pos('Buckets:' + #10 + #9 + '.skip 64', X86) > Tbss);
  AssertTrue('x86-64: A is ordinary data', (Pos(#10 + 'A:', X86) >= 0) and
    (Pos(#10 + 'A:', X86) < Tbss));
  AssertTrue('x86-64: thread-pointer access', Pos('Counter@tpoff', X86) >= 0);
  A64 := GenAsm(Src, TargetArm64);
  AssertTrue('arm64: thread_bss section', Pos('__thread_bss', A64) >= 0);
  AssertTrue('arm64: Counter storage', Pos(#10 + '_ts_Counter:', A64) >= 0);
  AssertTrue('arm64: Counter TLV descriptor', Pos(#10 + '_tv_Counter:', A64) >= 0);
  AssertTrue('arm64: Name TLV descriptor', Pos(#10 + '_tv_Name:', A64) >= 0);
  AssertTrue('arm64: Buckets is 64 bytes',
    Pos('_ts_Buckets:' + #10 + #9 + '.zero 64', A64) >= 0);
  AssertTrue('arm64: A is ordinary data', Pos('_tv_A', A64) < 0);
end;

procedure TThreadVarTests.TestCodegenNative_AddrOfThreadVar_UsesTls;
var
  Asm_: string;
begin
  Asm_ := Self.GenerateNativeAsm(
    'program P;' + #10 +
    'threadvar' + #10 +
    '  TV: Int64;' + #10 +
    'var' + #10 +
    '  Q: Pointer;' + #10 +
    'begin' + #10 +
    '  Q := @TV' + #10 +
    'end.');
  AssertTrue('@threadvar computes the thread pointer base (%fs:0)',
    Pos('movq %fs:0', Asm_) >= 0);
  AssertTrue('@threadvar offsets via TV@tpoff',
    Pos('TV@tpoff(', Asm_) >= 0);
  AssertTrue('@threadvar must NOT take the static address',
    Pos('leaq TV(%rip)', Asm_) < 0);
end;

procedure TThreadVarTests.TestCodegenNative_AddrOfPlainGlobal_StaysRipRelative;
var
  Asm_: string;
begin
  Asm_ := Self.GenerateNativeAsm(
    'program P;' + #10 +
    'var' + #10 +
    '  GV: Int64;' + #10 +
    '  Q: Pointer;' + #10 +
    'begin' + #10 +
    '  Q := @GV' + #10 +
    'end.');
  AssertTrue('@global stays PC-relative',
    Pos('leaq GV(%rip)', Asm_) >= 0);
  AssertTrue('@global takes no TLS path',
    Pos('GV@tpoff', Asm_) < 0);
end;

procedure TThreadVarTests.TestCodegen_RecordThreadVar_FieldStoreThroughTls;
const
  Src = '''
    program Prg;
    type TRec = record Tag: Integer; end;
    threadvar TVR: TRec;
    begin
      TVR.Tag := 4;
      WriteLn(TVR.Tag)
    end.
    ''';
begin
  AssertEquals('the field store goes through the thread-local address', '',
    AsmMissing(Src,
      #9'leaq TVR@tpoff(%rcx), %rcx'#10#9'popq %rax'#10#9'movl %eax, 0(%rcx)',
      #9'mov x9, x0'#10#9'ldr x0, [sp], #16'#10#9'str w0, [x9, #0]'));
end;

const
  SrcThreadVarShapes = '''
    program P;
    type
      IGreet = interface function Hi(): string; end;
      TC = class N: Integer; end;
      TR = record S: string; A, B: Integer; end;
    function Mk(): TR; begin Result.A := 1 end;
    threadvar
      A: array of Integer;
      S: string;
      G: IGreet;
      F: reference to procedure;
      C: TC;
      R: TR;
    procedure Fill(var X: IGreet); begin X := nil end;
    begin
      SetLength(A, 2);
      SetLength(S, 1);
      Delete(S, 0, 1);
      Fill(G);
      F := procedure begin WriteLn(A[0]) end;
      F();
      C := TC.Create();
      C.Free();
      R := Mk()
    end.
    ''';

procedure TThreadVarTests.TestCodegenX86_ThreadVarUpdates_NeverRipRelative;
var
  Asm_: string;
begin
  Asm_ := GenAsm(SrcThreadVarShapes, TargetX86_64);
  AssertTrue('SetLength on a dyn-array threadvar', Pos(' A(%rip)', Asm_) < 0);
  AssertTrue('SetLength / Delete on a string threadvar',
    Pos(' S(%rip)', Asm_) < 0);
  AssertTrue('Free nils a class threadvar', Pos(' C(%rip)', Asm_) < 0);
  AssertTrue('an sret result into a record threadvar',
    Pos(' R(%rip)', Asm_) < 0);
  AssertTrue('the dyn array is stored back through TLS',
    Pos(#9'movq %rax, %fs:A@tpoff', Asm_) >= 0);
  AssertTrue('Free clears the TLS slot', Pos(#9'movq $0, %fs:C@tpoff', Asm_) >= 0);
end;

procedure TThreadVarTests.TestCodegenX86_ThreadVarAddress_NeverLeaqThroughSegment;
var
  Asm_: string;
begin
  Asm_ := GenAsm(SrcThreadVarShapes, TargetX86_64);
  AssertTrue('no leaq through the %fs segment', Pos('leaq %fs:', Asm_) < 0);
  AssertTrue('the interface pair''s address is thread pointer + offset',
    Pos('leaq G_obj@tpoff(', Asm_) >= 0);
  AssertTrue('the closure''s address is thread pointer + offset',
    Pos('leaq F@tpoff(', Asm_) >= 0);
end;

procedure TThreadVarTests.TestCodegenX86_ThreadVarTbssLayout_MatchesPlainGlobals;
var
  Asm_: string;
begin
  Asm_ := GenAsm(SrcThreadVarShapes, TargetX86_64);
  AssertTrue('interface threadvar: obj+itab pair',
    Pos('G_obj:'#10#9'.skip 8'#10'G_itab:'#10#9'.skip 8', Asm_) >= 0);
  AssertTrue('closure threadvar: 16-byte Code+Env pair',
    Pos('F:'#10#9'.skip 16', Asm_) >= 0);
end;

procedure TThreadVarTests.TestCodegenArm64_ThreadVarStorage_SizedLikePlainGlobals;
var
  Asm_: string;
begin
  Asm_ := GenAsm(SrcThreadVarShapes, TargetArm64);
  AssertTrue('interface: obj+itab', Pos('_ts_G:'#10#9'.zero 16', Asm_) >= 0);
  AssertTrue('closure: Code+Env', Pos('_ts_F:'#10#9'.zero 16', Asm_) >= 0);
  AssertTrue('managed record: its full size',
    Pos('_ts_R:'#10#9'.zero 16', Asm_) >= 0);
  AssertTrue('dyn array: one pointer', Pos('_ts_A:'#10#9'.zero 8', Asm_) >= 0);
  AssertTrue('no ordinary global for the interface',
    Pos('_g_G', Asm_) < 0);
  AssertTrue('no ordinary global for the dyn array', Pos('_g_A', Asm_) < 0);
end;

procedure TThreadVarTests.TestCodegenArm64_IntfThreadVar_ItabAtTlvPlus8;
const
  Src = '''
    program P;
    type
      IGreet = interface function Hi(): string; end;
      TGreet = class(IGreet) function Hi(): string; end;
    function TGreet.Hi(): string; begin Result := 'hi' end;
    threadvar G: IGreet;
    begin
      G := TGreet.Create();
      WriteLn(G.Hi())
    end.
    ''';
var
  Asm_: string;
begin
  Asm_ := GenAsm(Src, TargetArm64);
  AssertTrue('the itab half is 8 bytes into the TLV',
    Pos('_tv_G@PAGEOFF'#10#9'ldr x9, [x0]'#10#9'blr x9'#10#9'add x0, x0, #8',
      Asm_) >= 0);
  AssertTrue('no separate itab global', Pos('_g_G_itab', Asm_) < 0);
end;

initialization
  RegisterTest(TThreadVarTests);

end.
