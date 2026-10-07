{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.external;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, cp.test.harness;

type
  TExternalTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function ParseUnit(const ASrc: string): TUnit;
    procedure AssertCodegenRefused(const AWhat, ASrc, ATarget: string);
  published
    { Parser — standalone procedure }
    procedure TestParse_ExternalProc_IsExternal;
    procedure TestParse_ExternalProc_ExternalNameEmpty;
    procedure TestParse_ExternalProcNamed_ExternalName;
    { Parser — library-qualified external records ExternalLib and hoists
      the bare library name into the program's LinkLibs set. }
    procedure TestParse_ExternalLibName_RecordsLibAndLinkLib;
    { Parser — standalone function }
    procedure TestParse_ExternalFunc_IsExternal;
    procedure TestParse_ExternalFuncNamed_ExternalName;
    { Parser — in unit interface section }
    procedure TestParse_ExternalInUnitInterface;
    { Semantic — external proc is registered and callable }
    procedure TestSemantic_ExternalProc_Callable;
    procedure TestSemantic_ExternalFunc_CallableAsExpr;
    { Codegen — no body emitted for external declarations }
    procedure TestCodegen_ExternalProc_NoBodyEmitted;
    { Codegen — call to external proc generates a call instruction }
    procedure TestCodegen_ExternalProc_CallEmitted;
    { Codegen — call uses C symbol name when 'external name' is given }
    procedure TestCodegen_ExternalProcNamed_UsesExternalName;
    { Codegen — narrow-int FFI returns must be normalised to their
      declared width at the call site.  C ABI leaves the upper bits of
      the return register undefined for sub-int returns, so a caller
      observing the value as a full word (e.g. `if Foo() <> 0 then`)
      would otherwise see garbage upper bits and mis-fire silently. }
    procedure TestCodegen_ExternalByteReturn_MaskedToLowByte;
    procedure TestCodegen_ExternalWordReturn_MaskedToLow16;
    procedure TestCodegen_ExternalSmallIntReturn_SignExtendedFromLow16;
    procedure TestCodegen_ExternalIntegerReturn_NoNormalisation;
    { A double-typed expression (literal, arithmetic result) passed to
      a Single FFI parameter must narrow to 4-byte float on the wire
      before the call.  Without the narrowing, 8 bytes of double go
      into the float-by-value slot and the C `float` callee reads the
      low mantissa half as IEEE-754 single — pure noise. }
    procedure TestCodegen_ExternalSingleParam_DoubleArgNarrowed;
    { A record passed by value to a cdecl external must go through the
      platform C ABI so the callee sees the struct contents in registers.  Passing
      the record's address in a single integer register would make the
      callee read the low bits of a pointer as struct data — e.g. a
      4-byte RGBA struct given to ClearBackground would clear the
      window to whatever colour fell out of the stack frame address. }
    procedure TestCodegen_ExternalRecordParam_PassedAsAggregateType;
    procedure TestCodegen_ExternalRecordParam_TwoEightbytes;
    procedure TestCodegen_ExternalRecordParam_FloatShape_NotSilent;
  end;

implementation

function TExternalTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TExternalTests.ParseUnit(const ASrc: string): TUnit;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
end;

{ ── Parser tests ─────────────────────────────────────────────────────────── }

procedure TExternalTests.TestParse_ExternalProc_IsExternal;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
        end.
        '''
  );
  try
    AssertEquals('Should have one proc decl', 1, Prog.Block.ProcDecls.Count);
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalProc_ExternalNameEmpty;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertEquals('ExternalName should be empty when no name given',
      '', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalProcNamed_ExternalName;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external name 'c_foo';
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
    AssertEquals('ExternalName should be c_foo', 'c_foo', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalLibName_RecordsLibAndLinkLib;
var
  Prog: TProgram;
  Decl: TMethodDecl;
  Lib:  TLinkLibDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function c_strlen(S: PChar): Integer; external 'c' name 'strlen';
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
    AssertEquals('ExternalName should be strlen', 'strlen', Decl.ExternalName);
    AssertEquals('ExternalLib should be c', 'c', Decl.ExternalLib);

    { The bare library name is hoisted into the program's LinkLibs set so
      the link layer can expand it to -l<name>. }
    AssertEquals('one link lib collected', 1, Prog.LinkLibs.Count);
    Lib := TLinkLibDecl(Prog.LinkLibs.Items[0]);
    AssertEquals('link lib name', 'c', Lib.LibName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalFunc_IsExternal;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external;
        begin
        end.
        '''
  );
  try
    AssertEquals('Should have one func decl', 1, Prog.Block.ProcDecls.Count);
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalFuncNamed_ExternalName;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external name 'c_bar';
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertEquals('ExternalName should be c_bar', 'c_bar', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalInUnitInterface;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyLib;
        interface
        procedure Foo; external;
        function Bar: Integer; external;
        implementation
        end.
        '''
  );
  try
    AssertEquals('Interface should have 2 proc decls',
      2, U.IntfBlock.ProcDecls.Count);
    AssertTrue('Foo should be external',
      TMethodDecl(U.IntfBlock.ProcDecls.Items[0]).IsExternal);
    AssertTrue('Bar should be external',
      TMethodDecl(U.IntfBlock.ProcDecls.Items[1]).IsExternal);
  finally
    U.Free();
  end;
end;

{ ── Semantic tests ───────────────────────────────────────────────────────── }

procedure TExternalTests.TestSemantic_ExternalProc_Callable;
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
          Foo()
        end.
        '''
  );
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

procedure TExternalTests.TestSemantic_ExternalFunc_CallableAsExpr;
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external;
        var x: Integer;
        begin
          x := Bar()
        end.
        '''
  );
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ── Codegen tests ────────────────────────────────────────────────────────── }

procedure TExternalTests.TestCodegen_ExternalProc_NoBodyEmitted;
const
  Src =
    '''
        program Test;
        procedure Foo; external;
        begin
          Foo()
        end.
        ''';
begin
  { An external declaration must NOT emit a body (no label) for Foo }
  AssertTrue('x86-64: no body for an external proc',
    Pos(#10'Foo:', GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('arm64: no body for an external proc',
    Pos(#10'_Foo:', GenAsm(Src, TargetArm64)) < 0);
end;

procedure TExternalTests.TestCodegen_ExternalProc_CallEmitted;
begin
  { no link name: the routine's own name is the C symbol }
  AssertEquals('call to the external proc', '', AsmMissing(
    '''
        program Test;
        procedure Foo; external;
        begin
          Foo()
        end.
        ''', 'callq Foo', 'bl _Foo'));
end;

procedure TExternalTests.TestCodegen_ExternalProcNamed_UsesExternalName;
const
  Src =
    '''
        program Test;
        procedure Foo; external name 'c_foo';
        begin
          Foo()
        end.
        ''';
begin
  { Call site must use the C symbol name, not the Pascal name }
  AssertEquals('call uses the C symbol name', '',
    AsmMissing(Src, 'callq c_foo', 'bl _c_foo'));
  AssertTrue('x86-64: Pascal name unused',
    Pos('callq Foo', GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('arm64: Pascal name unused',
    Pos('bl _Foo', GenAsm(Src, TargetArm64)) < 0);
end;

procedure TExternalTests.TestCodegen_ExternalByteReturn_MaskedToLowByte;
begin
  AssertEquals('Byte FFI return zero-extended from 8 bits', '', AsmMissing(
    '''
        program Test;
        function Foo: Byte; external;
        var v: Byte;
        begin
          v := Foo();
          if Foo() <> 0 then
            v := 1;
        end.
        ''', 'movzbq %al, %rax', 'lsr x0, x0, #56'));
end;

procedure TExternalTests.TestCodegen_ExternalWordReturn_MaskedToLow16;
begin
  AssertEquals('Word FFI return zero-extended from 16 bits', '', AsmMissing(
    '''
        program Test;
        function Foo: Word; external;
        var v: Word;
        begin
          v := Foo();
          if Foo() <> 0 then
            v := 1;
        end.
        ''', 'movzwq %ax, %rax', 'lsr x0, x0, #48'));
end;

procedure TExternalTests.TestCodegen_ExternalSmallIntReturn_SignExtendedFromLow16;
begin
  AssertEquals('SmallInt FFI return sign-extended from 16 bits', '', AsmMissing(
    '''
        program Test;
        function Foo: SmallInt; external;
        var v: SmallInt;
        begin
          v := Foo();
          if Foo() <> 0 then
            v := 1;
        end.
        ''', 'movswq %ax, %rax', 'asr x0, x0, #48'));
end;

procedure TExternalTests.TestCodegen_ExternalIntegerReturn_NoNormalisation;
const
  Src =
    '''
        program Test;
        function Foo: Integer; external;
        var v: Integer;
        begin
          v := Foo();
          if Foo() <> 0 then
            v := 1;
        end.
        ''';
var
  X86, A64: string;
begin
  { Full-width returns need no narrow fix-up. }
  X86 := GenAsm(Src, TargetX86_64);
  A64 := GenAsm(Src, TargetArm64);
  AssertTrue('x86-64: Integer FFI return not narrowed',
    (Pos('movzbq', X86) < 0) and (Pos('movzwq', X86) < 0) and
    (Pos('movswq', X86) < 0));
  AssertTrue('arm64: Integer FFI return not narrowed',
    (Pos('x0, #56', A64) < 0) and (Pos('x0, #48', A64) < 0));
end;

procedure TExternalTests.TestCodegen_ExternalSingleParam_DoubleArgNarrowed;
begin
  { Double literal narrowed to single before the call. }
  AssertEquals('Double-typed arg narrowed to Single before the FFI call', '',
    AsmMissing(
    '''
        program Test;
        function sinf(x: Single): Single; cdecl; external name 'sinf';
        var s: Single;
        begin
          s := sinf(1.5707964);
        end.
        ''', 'cvtsd2ss %xmm0, %xmm0', 'fcvt s0, d0'));
end;

procedure TExternalTests.TestCodegen_ExternalRecordParam_PassedAsAggregateType;
const
  Src =
    '''
        program Test;
        type
          TColor = record r, g, b, a: Byte; end;
        procedure CheckColor(c: TColor); cdecl; external name 'check_color';
        var c: TColor;
        begin
          c.r := 18; c.g := 18; c.b := 24; c.a := 255;
          CheckColor(c);
        end.
        ''';
begin
  { the record's 4 BYTES are loaded into the argument register -- not its
    address (BUG-20261007-x86-extern-record-byval) }
  AssertEquals('record bytes, not its address, reach the C callee', '',
    AsmMissing(Src, 'movl 0(%rcx), %eax', 'ldr x0, [x0]'));
  AssertTrue('x86-64: the address is not passed',
    Pos('leaq c(%rip), %rax' + #10#9'movq %rax, %rdi',
      GenAsm(Src, TargetX86_64)) < 0);
end;

procedure TExternalTests.TestCodegen_ExternalRecordParam_TwoEightbytes;
const
  Src =
    '''
        program Test;
        type
          TBox = record x, y, w: Integer; end;
        procedure Take(b: TBox; n: Integer); cdecl; external name 'take';
        var b: TBox;
        begin
          b.x := 1; b.y := 2; b.w := 3;
          Take(b, 4);
        end.
        ''';
var
  X86: string;
begin
  { 12 bytes, both eightbytes INTEGER: two registers (rdi, rsi / x0, x1),
    the next argument in the third }
  X86 := GenAsm(Src, TargetX86_64);
  AssertTrue('x86-64: first eightbyte loaded', Pos('movq 0(%rcx), %rax', X86) >= 0);
  AssertTrue('x86-64: second eightbyte loaded', Pos('movl 8(%rcx), %eax', X86) >= 0);
  AssertTrue('x86-64: the eightbytes land in rdi and rsi',
    (Pos('popq %rdi', X86) >= 0) and (Pos('popq %rsi', X86) >= 0));
  AssertTrue('x86-64: the Integer follows in rdx', Pos('%rdx', X86) >= 0);
  AssertTrue('arm64: both halves loaded',
    Pos('ldr x0, [x9, #8]', GenAsm(Src, TargetArm64)) >= 0);
end;

procedure TExternalTests.TestCodegen_ExternalRecordParam_FloatShape_NotSilent;
const
  Src =
    '''
        program Test;
        type
          TVec = record x, y: Single; end;
        procedure Take(v: TVec); cdecl; external name 'take';
        var v: TVec;
        begin
          Take(v);
        end.
        ''';
begin
  { a float-bearing record needs SSE / s registers: refused, never passed
    in the wrong registers }
  AssertCodegenRefused('x86-64', Src, TargetX86_64);
  AssertCodegenRefused('arm64', Src, TargetArm64);
end;

procedure TExternalTests.AssertCodegenRefused(const AWhat, ASrc,
  ATarget: string);
var
  Raised: Boolean;
begin
  Raised := False;
  try
    GenAsm(ASrc, ATarget);
  except
    on E: Exception do
      Raised := Pos('external routine', E.Message) >= 0;
  end;
  AssertTrue(AWhat + ': unsupported record shape is a code-generation error',
    Raised);
end;

initialization
  RegisterTest(TExternalTests);

end.
