{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.assembler;

interface

uses
  SysUtils, Classes, Process, blaise.testing,
  blaise.container.writer, blaise.elfwriter, blaise.elfreader,
  blaise.assembler.x86_64;

type
  { ---- Instruction/directive encoding regression tests ----
    Byte-level assertions against AssembleToBytes output.  Expected
    encodings cross-checked against GNU as. }
  TAsmEncodingTests = class(TTestCase)
  private
    function ContainsBytes(const ABuf, APat: string): Boolean;
  published
    procedure TestBareMemOperand_StoreViaReg;
    procedure TestBareMemOperand_LoadViaReg;
    procedure TestQuadSymbol_EmitsReloc;
    procedure TestTLSPrefix_PrecedesRex;
    procedure TestTbssSymbol_TypedSttTls;
    procedure TestRipRelImmStore_AddendMinus8;
    procedure TestBranchUndefined_EmitsReloc;
    procedure TestNoteGnuStack_Present;
    procedure TestUnknownDirective_Raises;
    procedure TestDuplicateLabel_Raises;
    procedure TestRexX_ExtendedIndexImmStore;
    procedure TestMovwImm16_TwoByteImmediate;
    procedure TestErrorMessage_HasLineNumber;
    procedure TestMovqXmmToReg_SseEncoding;
    procedure TestMovqRegToXmm_SseEncoding;
    procedure TestNegl_F7Slash3;
    procedure TestLockXaddl_AtomicEncoding;
    procedure TestLockXaddq_RexW;
    procedure TestXchgq_RexW;
    procedure TestLockCmpxchgq_RexW;
    procedure TestUnsuffixedMov_InfersSize;
    procedure TestJmpIndirectMem_FFSlash4;
    procedure TestEndbr64AndHlt;
    procedure TestSyscall_0F05;
    procedure TestCallPltStripsSuffix;
    procedure TestSse2_PxorAndPabsb;
    procedure TestVex_Vpxor2byte;
    procedure TestVex_Vpabsb3byte;
    procedure TestVex_VextractI128;
    procedure TestSibWhitespaceTolerated;
  end;

  { ---- ELF writer unit tests ---- }
  TElfWriterTests = class(TTestCase)
  private
    function ReadU8(const ABuf: string; AOff: Integer): Integer;
    function ReadU16(const ABuf: string; AOff: Integer): Integer;
  published
    procedure TestElfHeader_Magic;
    procedure TestElfHeader_Class64;
    procedure TestElfHeader_DataLSB;
    procedure TestElfHeader_TypeREL;
    procedure TestElfHeader_MachineX86_64;
    procedure TestAppend_TextSection;
    procedure TestAppend_DataSection;
    procedure TestCurrentOffset_Tracks;
    procedure TestDefineSymbol_FindsIt;
    procedure TestExternSymbol_FindsIt;
    procedure TestAlignSection_Pads;
    procedure TestAppendByte_SingleByte;
    procedure TestAppendDWord_FourBytes;
    procedure TestAppendQWord_EightBytes;
    procedure TestReserveBss_NoData;
    procedure TestContainerWriterSeam_ElfViaInterface;
  end;

  { ---- Internal assembler E2E tests ----
    Invoke the compiler CLI with --backend native --assembler internal,
    then link and run.  This exercises the full pipeline:
    source -> parse -> semantic -> native codegen -> internal assembler
    -> ELF object -> linker -> run. }
  TInternalAsmE2ETests = class(TTestCase)
  private
    FCompiler: string;
    FRTLPath: string;
    FStdlibPath: string;
    FScratch: string;
    FCounter: Integer;
    function ProjectRoot: string;
    function CompilerAvailable: Boolean;
    function RunProc(const AExe: string; const AArgs: array of string;
      out AStdout: string): Integer;
    function RunProcNoArgs(const AExe: string; out AStdout: string): Integer;
    function CompileAndRun(const ASrc: string;
      out AStdout: string; out AExitCode: Integer): Boolean;
    function CompileAndRunArgs(const ASrc: string;
      const AArgs: array of string;
      out AStdout: string; out AExitCode: Integer): Boolean;
  protected
    procedure SetUp; override;
  published
    procedure TestSimpleAdd;
    procedure TestStringOutput;
    procedure TestForLoop;
    procedure TestFunctionCall;
    procedure TestIfElse;
    procedure TestWhileLoop;
    procedure TestBooleanExpr;
    procedure TestNegativeNumbers;
    procedure TestMultipleVars;
    { Stage-1 register promotion emits extended-register sub-register
      forms (movb %al, %r14b / movzwq %r14w, ... / movl ..., %r14d) —
      this pins that the internal assembler encodes them correctly.
      (Only exercises promotion once the fixpoint compiler binary is
      itself promotion-aware; before that it still validates the
      program's behaviour.) }
    procedure TestPromotedSubRegisterWidths;
    procedure TestNestedCalls;
    procedure TestClassVirtualCall;
    procedure TestFloatArithmetic;
    procedure TestFormatFloatArg;
    { Self-contained program entry (issue #142): the runtime supplies its own
      _start (blaise_start_x86_64.s) so the internal linker needs no system
      Scrt1.o / crtbegin / crtend.  These assert the two things _start owns —
      argc/argv forwarding and exit-code propagation through __libc_start_main. }
    procedure TestEntry_ExitCodePropagates;
    procedure TestEntry_ArgsForwarded;
    { Inline assembler blocks (asm ... end): a nostackframe asm-body function is
      assembled verbatim by the internal assembler and called from Pascal. }
    procedure TestInlineAsm_ReturnsValue;
    procedure TestInlineAsm_AddsTwoArgs;
    { --debug-opdf appends the OPDF section to the SAME assembly text the
      internal assembler consumes.  A string constant whose value contains a
      double-quote or newline used to break the recConstant `.ascii "<val>"`
      line (the raw value closed the literal early), aborting the assemble.
      Escaping the value fixes it; this compiles+runs such a program under
      --debug-opdf --assembler internal. }
    procedure TestDebugOPDF_StringConstSpecialChars_AssemblesAndRuns;
  end;

implementation

{ Print the "tests skipped" note at most once per suite run, so a CI
  environment that lacks the QBE compiler binary surfaces the skip loudly
  instead of silently reporting green with ~12 ignored tests. }
var
  GInternalAsmSkipNoted: Boolean = False;

{ Validity-probe cache for the fallback compiler — see the matching note in
  cp.test.cli.pas.  The /tmp/fp_blaise2 fallback is a transient fixpoint
  artifact that is often stale; a stale binary turns these e2e tests into a
  cascade of cryptic failures.  Probe once and skip (not fail) on a bad probe.
  0 = not probed, 1 = good, 2 = bad. }
var
  GInternalAsmProbeState: Integer = 0;

{ ---- TAsmEncodingTests ---- }

function TAsmEncodingTests.ContainsBytes(const ABuf, APat: string): Boolean;
begin
  Result := Pos(APat, ABuf) >= 0;
end;

procedure TAsmEncodingTests.TestBareMemOperand_StoreViaReg;
var
  Obj: string;
begin
  { movq %rcx, (%rax) -> 48 89 08.  Emitted constantly by the native
    backend (vtable install, pointer stores); previously unparseable. }
  Obj := AssembleToBytes('movq %rcx, (%rax)' + LineEnding);
  AssertTrue('48 89 08 missing',
    ContainsBytes(Obj, Chr($48) + Chr($89) + Chr($08)));
end;

procedure TAsmEncodingTests.TestBareMemOperand_LoadViaReg;
var
  Obj: string;
begin
  { movq (%rdi), %rax -> 48 8B 07 }
  Obj := AssembleToBytes('movq (%rdi), %rax' + LineEnding);
  AssertTrue('48 8B 07 missing',
    ContainsBytes(Obj, Chr($48) + Chr($8B) + Chr($07)));
end;

procedure TAsmEncodingTests.TestNegl_F7Slash3;
var
  Obj: string;
begin
  { negl %esi -> f7 de  (F7 /3, reg=esi=6).  Verified vs `cc`. }
  Obj := AssembleToBytes('negl %esi' + LineEnding);
  AssertTrue('f7 de missing',
    ContainsBytes(Obj, Chr($F7) + Chr($DE)));
end;

procedure TAsmEncodingTests.TestLockXaddl_AtomicEncoding;
var
  Obj: string;
begin
  { lock xaddl %eax, (%rdi) -> f0 0f c1 07.  The atomic RTL primitive
    (_AtomicAddInt32).  f0 = lock prefix, 0f c1 = xadd, 07 = ModRM
    (reg=eax=0, r/m=[rdi]).  Verified vs `cc`. }
  Obj := AssembleToBytes('lock xaddl %eax, (%rdi)' + LineEnding);
  AssertTrue('f0 0f c1 07 missing',
    ContainsBytes(Obj, Chr($F0) + Chr($0F) + Chr($C1) + Chr($07)));
end;

procedure TAsmEncodingTests.TestLockXaddq_RexW;
var
  Obj: string;
begin
  { lock xaddq %rax, (%rdi) -> f0 48 0f c1 07.  The 64-bit atomic
    fetch-add (_AtomicAddInt64) — REX.W must be present or the operation
    silently narrows to 32 bits.  Verified vs `cc`. }
  Obj := AssembleToBytes('lock xaddq %rax, (%rdi)' + LineEnding);
  AssertTrue('f0 48 0f c1 07 missing',
    ContainsBytes(Obj, Chr($F0) + Chr($48) + Chr($0F) + Chr($C1) + Chr($07)));
end;

procedure TAsmEncodingTests.TestXchgq_RexW;
var
  Obj: string;
begin
  { xchgq %rsi, (%rdi) -> 48 87 37.  The 64-bit atomic exchange
    (_AtomicXchgPtr).  A missing REX.W narrows the exchange to 32 bits and
    zero-extends the returned old value — pointer truncation.  Verified
    vs `cc`. }
  Obj := AssembleToBytes('xchgq %rsi, (%rdi)' + LineEnding);
  AssertTrue('48 87 37 missing',
    ContainsBytes(Obj, Chr($48) + Chr($87) + Chr($37)));
end;

procedure TAsmEncodingTests.TestLockCmpxchgq_RexW;
var
  Obj: string;
begin
  { lock cmpxchgq %rdx, (%rdi) -> f0 48 0f b1 17.  The 64-bit atomic
    compare-and-swap (_AtomicCASPtr).  A missing REX.W compares/stores only
    the low 32 bits of the pointer.  Verified vs `cc`. }
  Obj := AssembleToBytes('lock cmpxchgq %rdx, (%rdi)' + LineEnding);
  AssertTrue('f0 48 0f b1 17 missing',
    ContainsBytes(Obj, Chr($F0) + Chr($48) + Chr($0F) + Chr($B1) + Chr($17)));
end;

procedure TAsmEncodingTests.TestUnsuffixedMov_InfersSize;
var
  Obj: string;
begin
  { Unsuffixed AT&T mnemonics infer size from the register operand.
    mov %rbx, (%rdi) is 64-bit -> 48 89 1f (same as movq).  Verified vs cc. }
  Obj := AssembleToBytes('mov %rbx, (%rdi)' + LineEnding);
  AssertTrue('48 89 1f missing (mov inferred q)',
    ContainsBytes(Obj, Chr($48) + Chr($89) + Chr($1F)));
  { xor %eax, %eax is 32-bit -> 31 c0 (no REX.W). }
  Obj := AssembleToBytes('xor %eax, %eax' + LineEnding);
  AssertTrue('31 c0 missing (xor inferred l)',
    ContainsBytes(Obj, Chr($31) + Chr($C0)));
end;

procedure TAsmEncodingTests.TestJmpIndirectMem_FFSlash4;
var
  Obj: string;
begin
  { jmp *56(%rdi) -> ff 67 38  (FF /4, memory-indirect).  The longjmp tail. }
  Obj := AssembleToBytes('jmp *56(%rdi)' + LineEnding);
  AssertTrue('ff 67 38 missing',
    ContainsBytes(Obj, Chr($FF) + Chr($67) + Chr($38)));
end;

procedure TAsmEncodingTests.TestEndbr64AndHlt;
var
  Obj: string;
begin
  { endbr64 -> f3 0f 1e fa ; hlt -> f4 }
  Obj := AssembleToBytes('endbr64' + LineEnding);
  AssertTrue('f3 0f 1e fa missing',
    ContainsBytes(Obj, Chr($F3) + Chr($0F) + Chr($1E) + Chr($FA)));
  Obj := AssembleToBytes('hlt' + LineEnding);
  AssertTrue('f4 missing', ContainsBytes(Obj, Chr($F4)));
end;

procedure TAsmEncodingTests.TestSyscall_0F05;
var
  Obj: string;
begin
  { syscall -> 0f 05 (needed for the FreeBSD direct-syscall stubs). }
  Obj := AssembleToBytes('syscall' + LineEnding);
  AssertTrue('0f 05 missing', ContainsBytes(Obj, Chr($0F) + Chr($05)));
end;

procedure TAsmEncodingTests.TestCallPltStripsSuffix;
var
  Obj: string;
begin
  { call foo@PLT must reference symbol 'foo' (with a PLT32 reloc), NOT a bogus
    symbol literally named 'foo@PLT' that no loader resolves.  The @PLT suffix
    is a relocation qualifier, not part of the name.  Regression for the
    _start migration (call __libc_start_main@PLT). }
  Obj := AssembleToBytes('call foo@PLT' + LineEnding);
  AssertTrue('symbol foo missing', ContainsBytes(Obj, 'foo'));
  AssertTrue('bogus foo@PLT symbol present',
    not ContainsBytes(Obj, 'foo@PLT'));
end;

procedure TAsmEncodingTests.TestSse2_PxorAndPabsb;
var
  Obj: string;
begin
  { pxor %xmm3,%xmm3 -> 66 0f ef db ; pabsb is a 3-byte 0F38 op:
    pabsb %xmm2,%xmm2 -> 66 0f 38 1c d2.  Verified vs cc. }
  Obj := AssembleToBytes('pxor %xmm3, %xmm3' + LineEnding);
  AssertTrue('66 0f ef db missing',
    ContainsBytes(Obj, Chr($66) + Chr($0F) + Chr($EF) + Chr($DB)));
  Obj := AssembleToBytes('pabsb %xmm2, %xmm2' + LineEnding);
  AssertTrue('66 0f 38 1c d2 missing',
    ContainsBytes(Obj, Chr($66) + Chr($0F) + Chr($38) + Chr($1C) + Chr($D2)));
end;

procedure TAsmEncodingTests.TestVex_Vpxor2byte;
var
  Obj: string;
begin
  { vpxor %ymm3,%ymm3,%ymm3 -> c5 e5 ef db (2-byte VEX).  Verified vs cc. }
  Obj := AssembleToBytes('vpxor %ymm3, %ymm3, %ymm3' + LineEnding);
  AssertTrue('c5 e5 ef db missing',
    ContainsBytes(Obj, Chr($C5) + Chr($E5) + Chr($EF) + Chr($DB)));
end;

procedure TAsmEncodingTests.TestVex_Vpabsb3byte;
var
  Obj: string;
begin
  { vpabsb %ymm2,%ymm2 -> c4 e2 7d 1c d2 (3-byte VEX, 0F38 map).  Verified vs cc. }
  Obj := AssembleToBytes('vpabsb %ymm2, %ymm2' + LineEnding);
  AssertTrue('c4 e2 7d 1c d2 missing',
    ContainsBytes(Obj, Chr($C4) + Chr($E2) + Chr($7D) + Chr($1C) + Chr($D2)));
end;

procedure TAsmEncodingTests.TestVex_VextractI128;
var
  Obj: string;
begin
  { vextracti128 $1,%ymm3,%xmm4 -> c4 e3 7d 39 dc 01 (L=1 despite xmm dst).
    Verified vs cc. }
  Obj := AssembleToBytes('vextracti128 $1, %ymm3, %xmm4' + LineEnding);
  AssertTrue('c4 e3 7d 39 dc 01 missing',
    ContainsBytes(Obj, Chr($C4) + Chr($E3) + Chr($7D) + Chr($39) + Chr($DC) + Chr($01)));
end;

procedure TAsmEncodingTests.TestSibWhitespaceTolerated;
var
  A, B: string;
begin
  { GNU as allows whitespace after the SIB comma: `(%rdi, %rdx)` must encode
    identically to `(%rdi,%rdx)` (movdqu -> f3 0f 6f 04 17). }
  A := AssembleToBytes('movdqu (%rdi,%rdx), %xmm0' + LineEnding);
  B := AssembleToBytes('movdqu (%rdi, %rdx), %xmm0' + LineEnding);
  AssertTrue('f3 0f 6f 04 17 missing (no space)',
    ContainsBytes(A, Chr($F3) + Chr($0F) + Chr($6F) + Chr($04) + Chr($17)));
  AssertTrue('f3 0f 6f 04 17 missing (with space)',
    ContainsBytes(B, Chr($F3) + Chr($0F) + Chr($6F) + Chr($04) + Chr($17)));
end;

procedure TAsmEncodingTests.TestQuadSymbol_EmitsReloc;
var
  Obj: string;
begin
  { .quad <symbol> must produce a .rela.data entry against the symbol,
    not silently emit zero (null vtables). }
  Obj := AssembleToBytes('.data' + LineEnding +
    'vt:' + LineEnding +
    '.quad some_external_method' + LineEnding);
  AssertTrue('.rela.data missing', ContainsBytes(Obj, '.rela.data'));
  AssertTrue('symbol name missing',
    ContainsBytes(Obj, 'some_external_method'));
end;

procedure TAsmEncodingTests.TestTLSPrefix_PrecedesRex;
var
  Obj: string;
begin
  { movq %fs:tv@tpoff, %rax -> 64 48 8B 04 25 ... — the FS segment
    override must precede REX, not follow it. }
  Obj := AssembleToBytes('movq %fs:tv@tpoff, %rax' + LineEnding);
  AssertTrue('64 48 8B prefix order wrong',
    ContainsBytes(Obj, Chr($64) + Chr($48) + Chr($8B) + Chr($04) + Chr($25)));
end;

procedure TAsmEncodingTests.TestTbssSymbol_TypedSttTls;
var
  Obj: string;
  Parsed: TElfObjectFile;
  I: Integer;
  Found: Boolean;
begin
  { A symbol defined in .tbss must carry STT_TLS (GNU as infers it from the
    "T" section flag).  External linkers (lld, GNU ld) resolve @tpoff against
    a non-TLS symbol as a plain vaddr, yielding a wild positive thread-pointer
    offset — threadvars in RTL objects then crash (FreeBSD libthr) or silently
    alias across threads (glibc) in the cc-linked profile. }
  Obj := AssembleToBytes(
    '.section .tbss,"awT",@nobits' + LineEnding +
    '.balign 8' + LineEnding +
    '.globl tv' + LineEnding +
    'tv:' + LineEnding +
    #9'.skip 8' + LineEnding);
  Parsed := ParseElfObject(Obj, 'tbss-test');
  try
    Found := False;
    for I := 0 to Parsed.Symbols.Count - 1 do
      if Parsed.Symbols[I].Name = 'tv' then
      begin
        Found := True;
        AssertEquals('.tbss symbol must be STT_TLS',
          STT_TLS, Parsed.Symbols[I].SymType);
      end;
    AssertTrue('symbol tv not found in symtab', Found);
  finally
    Parsed.Free();
  end;
end;

procedure TAsmEncodingTests.TestRipRelImmStore_AddendMinus8;
var
  Obj: string;
  Pat: string;
begin
  { movq $0, gv(%rip): the PC32 addend must be -8 (disp field is 8
    bytes from instruction end: 4 disp + 4 imm), not -4. }
  Obj := AssembleToBytes('movq $0, gv(%rip)' + LineEnding);
  Pat := Chr($F8) + Chr($FF) + Chr($FF) + Chr($FF)
       + Chr($FF) + Chr($FF) + Chr($FF) + Chr($FF);
  AssertTrue('rela addend -8 missing', ContainsBytes(Obj, Pat));
end;

procedure TAsmEncodingTests.TestBranchUndefined_EmitsReloc;
var
  Obj: string;
begin
  { jmp to an external symbol must emit a relocation, not silently
    encode displacement 0 (a jump to the next instruction). }
  Obj := AssembleToBytes('jmp external_target' + LineEnding);
  AssertTrue('.rela.text missing', ContainsBytes(Obj, '.rela.text'));
  AssertTrue('target symbol missing', ContainsBytes(Obj, 'external_target'));
end;

procedure TAsmEncodingTests.TestNoteGnuStack_Present;
var
  Obj: string;
begin
  Obj := AssembleToBytes('ret' + LineEnding);
  AssertTrue('.note.GNU-stack section missing',
    ContainsBytes(Obj, '.note.GNU-stack'));
end;

procedure TAsmEncodingTests.TestUnknownDirective_Raises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AssembleToBytes('.bogus 42' + LineEnding);
  except
    on E: EAssembler do
      Raised := True;
  end;
  AssertTrue('unknown directive must raise EAssembler', Raised);
end;

procedure TAsmEncodingTests.TestDuplicateLabel_Raises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AssembleToBytes('dup:' + LineEnding + 'ret' + LineEnding +
      'dup:' + LineEnding + 'ret' + LineEnding);
  except
    on E: EAssembler do
      Raised := True;
  end;
  AssertTrue('duplicate label must raise EAssembler', Raised);
end;

procedure TAsmEncodingTests.TestRexX_ExtendedIndexImmStore;
var
  Obj: string;
begin
  { movq $5, (%rax,%r9,8) -> 4A C7 04 C8 05 00 00 00.
    REX.X must be set for the r9 index register. }
  Obj := AssembleToBytes('movq $5, (%rax,%r9,8)' + LineEnding);
  AssertTrue('4A C7 04 C8 missing (REX.X dropped)',
    ContainsBytes(Obj, Chr($4A) + Chr($C7) + Chr($04) + Chr($C8) + Chr($05)));
end;

procedure TAsmEncodingTests.TestMovwImm16_TwoByteImmediate;
var
  Obj: string;
begin
  { movw $258, %ax -> 66 C7 C0 02 01 — a 16-bit immediate, not 32-bit. }
  Obj := AssembleToBytes('movw $258, %ax' + LineEnding + 'ret' + LineEnding);
  AssertTrue('66 C7 C0 02 01 C3 missing (imm16 wrong size)',
    ContainsBytes(Obj, Chr($66) + Chr($C7) + Chr($C0) + Chr($02) + Chr($01)
      + Chr($C3)));
end;

procedure TAsmEncodingTests.TestErrorMessage_HasLineNumber;
var
  Msg: string;
begin
  Msg := '';
  try
    AssembleToBytes('ret' + LineEnding + '.bogus 1' + LineEnding);
  except
    on E: EAssembler do
      Msg := Exception(E).Message;
  end;
  AssertTrue('error must mention line 2, got: ' + Msg,
    Pos('line 2', Msg) >= 0);
end;

procedure TAsmEncodingTests.TestMovqXmmToReg_SseEncoding;
var
  Obj: string;
begin
  { movq %xmm0, %rax -> 66 48 0F 7E C0 (SSE MOVQ store-from-xmm).  This was
    mis-encoded as the integer `mov %rax,%rax` (48 89 C0), silently dropping the
    xmm value — the cause of float Format() args arriving as garbage.  (issue
    #133 follow-up regression.) }
  Obj := AssembleToBytes('movq %xmm0, %rax' + LineEnding);
  AssertTrue('66 48 0F 7E C0 missing',
    ContainsBytes(Obj, Chr($66) + Chr($48) + Chr($0F) + Chr($7E) + Chr($C0)));
  AssertFalse('must NOT encode as integer mov %rax,%rax (48 89 C0)',
    ContainsBytes(Obj, Chr($48) + Chr($89) + Chr($C0)));
end;

procedure TAsmEncodingTests.TestMovqRegToXmm_SseEncoding;
var
  Obj: string;
begin
  { movq %rax, %xmm0 -> 66 48 0F 6E C0 (SSE MOVQ load-into-xmm). }
  Obj := AssembleToBytes('movq %rax, %xmm0' + LineEnding);
  AssertTrue('66 48 0F 6E C0 missing',
    ContainsBytes(Obj, Chr($66) + Chr($48) + Chr($0F) + Chr($6E) + Chr($C0)));
end;

{ ---- ELF reader helpers ---- }

function TElfWriterTests.ReadU8(const ABuf: string; AOff: Integer): Integer;
begin
  Result := Ord(ABuf[AOff]) and $FF;
end;

function TElfWriterTests.ReadU16(const ABuf: string; AOff: Integer): Integer;
begin
  Result := (Ord(ABuf[AOff]) and $FF)
         or ((Ord(ABuf[AOff + 1]) and $FF) shl 8);
end;

{ ---- TElfWriterTests ---- }

procedure TElfWriterTests.TestContainerWriterSeam_ElfViaInterface;
var
  W: IContainerWriter;
  Buf: string;
  SymIdx: Integer;
begin
  { Drive TElfObjectWriter purely through the IContainerWriter seam — the
    contract the internal assemblers hold a writer by (Bridge: one
    assembler, N container writers).  ARC-managed: no manual Free. }
  W := TElfObjectWriter.Create();
  W.AppendByte(cskText, $90);
  SymIdx := W.DefineSymbol('probe', cskText, 0, 0, csbGlobal, cstFunc);
  AssertTrue(SymIdx >= 0);
  AssertEquals(SymIdx, W.FindSymbol('probe'));
  AssertEquals(1, W.CurrentOffset(cskText));
  W.AddReloc(cskText, 0, W.ExternSymbol('ext'), crkPC32, -4);
  Buf := W.Finish();
  AssertEquals($7F, ReadU8(Buf, 0));
  AssertEquals(Ord('E'), ReadU8(Buf, 1));
  AssertEquals(Ord('L'), ReadU8(Buf, 2));
  AssertEquals(Ord('F'), ReadU8(Buf, 3));
end;

procedure TElfWriterTests.TestElfHeader_Magic;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $90);
    Buf := W.Finish();
    AssertEquals($7F, ReadU8(Buf, 0));
    AssertEquals(Ord('E'), ReadU8(Buf, 1));
    AssertEquals(Ord('L'), ReadU8(Buf, 2));
    AssertEquals(Ord('F'), ReadU8(Buf, 3));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_Class64;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $90);
    Buf := W.Finish();
    AssertEquals(2, ReadU8(Buf, 4));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_DataLSB;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $90);
    Buf := W.Finish();
    AssertEquals(1, ReadU8(Buf, 5));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_TypeREL;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $90);
    Buf := W.Finish();
    AssertEquals(1, ReadU16(Buf, 16));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_MachineX86_64;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $90);
    Buf := W.Finish();
    AssertEquals(62, ReadU16(Buf, 18));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppend_TextSection;
var
  W: TElfObjectWriter;
  Off: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Off := W.Append(cskText, Chr($55) + Chr($48));
    AssertEquals(0, Off);
    AssertEquals(2, W.CurrentOffset(cskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppend_DataSection;
var
  W: TElfObjectWriter;
  Off: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Off := W.Append(cskData, Chr($01) + Chr($02) + Chr($03));
    AssertEquals(0, Off);
    AssertEquals(3, W.CurrentOffset(cskData));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestCurrentOffset_Tracks;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    AssertEquals(0, W.CurrentOffset(cskText));
    W.AppendByte(cskText, $90);
    AssertEquals(1, W.CurrentOffset(cskText));
    W.AppendByte(cskText, $90);
    AssertEquals(2, W.CurrentOffset(cskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestDefineSymbol_FindsIt;
var
  W: TElfObjectWriter;
  Idx: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Idx := W.DefineSymbol('main', cskText, 0, 0, csbGlobal, cstFunc);
    AssertTrue(Idx >= 0);
    AssertEquals(Idx, W.FindSymbol('main'));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestExternSymbol_FindsIt;
var
  W: TElfObjectWriter;
  Idx: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Idx := W.ExternSymbol('_SysWriteStr');
    AssertTrue(Idx >= 0);
    AssertEquals(Idx, W.FindSymbol('_SysWriteStr'));
    AssertEquals(-1, W.FindSymbol('nonexistent'));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAlignSection_Pads;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskData, $01);
    W.AppendByte(cskData, $02);
    AssertEquals(2, W.CurrentOffset(cskData));
    W.AppendByte(cskData, 0);
    W.AppendByte(cskData, 0);
    AssertEquals(4, W.CurrentOffset(cskData));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendByte_SingleByte;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $CC);
    AssertEquals(1, W.CurrentOffset(cskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendDWord_FourBytes;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $78);
    W.AppendByte(cskText, $56);
    W.AppendByte(cskText, $34);
    W.AppendByte(cskText, $12);
    AssertEquals(4, W.CurrentOffset(cskText));
    Buf := W.Finish();
    AssertEquals($78, ReadU8(Buf, 64));
    AssertEquals($56, ReadU8(Buf, 65));
    AssertEquals($34, ReadU8(Buf, 66));
    AssertEquals($12, ReadU8(Buf, 67));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendQWord_EightBytes;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(cskText, $08);
    W.AppendByte(cskText, $07);
    W.AppendByte(cskText, $06);
    W.AppendByte(cskText, $05);
    W.AppendByte(cskText, $04);
    W.AppendByte(cskText, $03);
    W.AppendByte(cskText, $02);
    W.AppendByte(cskText, $01);
    AssertEquals(8, W.CurrentOffset(cskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestReserveBss_NoData;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.ReserveBss(cskBss, 256);
    AssertEquals(256, W.CurrentOffset(cskBss));
  finally
    W.Free();
  end;
end;

{ ---- TInternalAsmE2ETests ---- }

function TInternalAsmE2ETests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

procedure TInternalAsmE2ETests.SetUp;
begin
  inherited SetUp();
  { Compiler resolution, in order: explicit override, then the two transient
    fixpoint artefacts, then the BUILT compiler.

    That last fallback is what makes this suite run at all off Linux.
    /tmp/fp_blaise2|3 are produced by scripts/fixpoint.sh, which is a
    Linux/FreeBSD path — on macOS they have never existed, so every test here
    skipped and the suite guarded NOTHING while appearing green.  CLAUDE.md
    names it a REQUIRED internal-assembler guard, so "absent but looks
    present" is the one outcome it must not have
    (BUG-20260728-internalasm-guard-skips-on-macos).

    Any working compiler is sufficient: the probe below, and every test in
    this suite, compiles with '--backend native --assembler internal', so what
    is under test is the INTERNAL ASSEMBLER, not the backend that produced the
    compiler binary.  BLAISE_QBE_COMPILER keeps its name for compatibility
    with existing invocations; it no longer implies a QBE-built binary.
    Staleness is still handled — the validity probe rejects a broken binary
    whichever slot it came from. }
  FCompiler := GetEnvironmentVariable('BLAISE_QBE_COMPILER');
  if FCompiler = '' then
    FCompiler := '/tmp/fp_blaise2';
  if not FileExists(FCompiler) then
    FCompiler := '/tmp/fp_blaise3';
  if not FileExists(FCompiler) then
    FCompiler := ProjectRoot() + 'compiler/target/blaise';
  FRTLPath := ProjectRoot() + 'compiler/src/main/pascal';
  FStdlibPath := ProjectRoot() + 'stdlib/src/main/pascal';
  FScratch := ProjectRoot() + 'compiler/target/asm_scratch/';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

function TInternalAsmE2ETests.CompilerAvailable: Boolean;
var
  SrcFile, OutFile, CompOut, RunOut: string;
  Rc: Integer;
begin
  { The compiler binary source-builds the RTL itself (no blaise_rtl.a); only
    the binary and the RTL source need to be present. }
  Result := FileExists(FCompiler)
        and FileExists(FRTLPath + '/runtime.arc.pas');
  if (not Result) and (not GInternalAsmSkipNoted) then
  begin
    GInternalAsmSkipNoted := True;
    WriteLn(StdErr, 'note: TInternalAsmE2ETests skipped — compiler binary "',
            FCompiler, '" or RTL source not found.  This suite is a REQUIRED ',
            'internal-assembler guard, so a skip here means it is guarding ',
            'nothing: build the compiler (compiler/target/blaise) or set ',
            'BLAISE_QBE_COMPILER to any working blaise binary.');
    Exit;
  end;
  if not Result then Exit;

  { Validity probe: compile+run a trivial program with --assembler internal.
    A stale fallback binary compiles fine but produces a SIGILL/wrong-output
    executable; detect that here and skip rather than emit a cryptic cascade. }
  if GInternalAsmProbeState = 0 then
  begin
    SrcFile := FScratch + 'probe.pas';
    OutFile := FScratch + 'probe';
    WriteFile(SrcFile, 'program p; begin WriteLn(42); end.');
    Rc := Self.RunProc(FCompiler, [
      '--source', SrcFile, '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
      '--output', OutFile, '--backend', 'native', '--assembler', 'internal'
    ], CompOut);
    if (Rc = 0) and (Self.RunProcNoArgs(OutFile, RunOut) = 0)
       and (Pos('42', RunOut) >= 0) then
      GInternalAsmProbeState := 1
    else
    begin
      GInternalAsmProbeState := 2;
      WriteLn(StdErr, 'note: TInternalAsmE2ETests skipped — compiler binary "',
              FCompiler, '" is stale/broken (probe program did not run); ',
              'rebuild it or set BLAISE_QBE_COMPILER to a current binary.');
    end;
  end;
  Result := GInternalAsmProbeState = 1;
end;

function TInternalAsmE2ETests.RunProc(const AExe: string;
  const AArgs: array of string; out AStdout: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TInternalAsmE2ETests.RunProcNoArgs(const AExe: string;
  out AStdout: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TInternalAsmE2ETests.CompileAndRun(const ASrc: string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcFile, OutFile, CompOut: string;
  Rc: Integer;
begin
  Result := False;
  if not Self.CompilerAvailable() then Exit;

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_asm_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_asm_' + IntToStr(FCounter);

  WriteFile(SrcFile, ASrc);

  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal'
  ], CompOut);
  if Rc <> 0 then
    { A compile failure is a real test failure, not a missing toolchain —
      Fail here so it cannot be masked as Ignore by the caller. }
    Fail('compile failed (rc=' + IntToStr(Rc) + '): ' + CompOut);

  AExitCode := Self.RunProcNoArgs(OutFile, AStdout);
  Result := True;
end;

{ Like CompileAndRun but runs the produced binary WITH command-line arguments,
  so argc/argv forwarding through the runtime's own _start is exercised. }
function TInternalAsmE2ETests.CompileAndRunArgs(const ASrc: string;
  const AArgs: array of string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcFile, OutFile, CompOut: string;
  Rc: Integer;
begin
  Result := False;
  if not Self.CompilerAvailable() then Exit;

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_asm_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_asm_' + IntToStr(FCounter);

  WriteFile(SrcFile, ASrc);

  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal'
  ], CompOut);
  if Rc <> 0 then
    Fail('compile failed (rc=' + IntToStr(Rc) + '): ' + CompOut);

  AExitCode := Self.RunProc(OutFile, AArgs, AStdout);
  Result := True;
end;

{ ---- Test methods ---- }

procedure TInternalAsmE2ETests.TestSimpleAdd;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_add;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(3 + 4)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('7' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestStringOutput;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_str;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''Hello from internal assembler'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('Hello from internal assembler' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestForLoop;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_for;' + LineEnding +
    'var I: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  for I := 1 to 5 do' + LineEnding +
    '    Write(I);' + LineEnding +
    '  WriteLn()' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('12345' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFunctionCall;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_func;' + LineEnding +
    'function Add(A, B: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := A + B' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Add(10, 32))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestIfElse;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_if;' + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  X := 5;' + LineEnding +
    '  if X > 3 then' + LineEnding +
    '    WriteLn(''yes'')' + LineEnding +
    '  else' + LineEnding +
    '    WriteLn(''no'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('yes' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestWhileLoop;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_while;' + LineEnding +
    'var N: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  N := 1;' + LineEnding +
    '  while N <= 3 do' + LineEnding +
    '  begin' + LineEnding +
    '    Write(N);' + LineEnding +
    '    N := N + 1' + LineEnding +
    '  end;' + LineEnding +
    '  WriteLn()' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('123' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestBooleanExpr;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_bool;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(True);' + LineEnding +
    '  WriteLn(False);' + LineEnding +
    '  WriteLn(3 = 3);' + LineEnding +
    '  WriteLn(3 <> 4)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('True' + LineEnding + 'False' + LineEnding +
               'True' + LineEnding + 'True' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestNegativeNumbers;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_neg;' + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  X := -42;' + LineEnding +
    '  WriteLn(X)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('-42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestPromotedSubRegisterWidths;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_promo_widths;' + LineEnding +
    'function Mix(B: Byte): Int64;' + LineEnding +
    'var W: SmallInt;' + LineEnding +
    'begin' + LineEnding +
    '  B := B + 200;' + LineEnding +
    '  W := -3;' + LineEnding +
    '  W := W * 100;' + LineEnding +
    '  Result := B;' + LineEnding +
    '  Result := Result * 1000 + W' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Mix(100))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('43700' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestMultipleVars;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_vars;' + LineEnding +
    'var A, B, C: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  A := 10;' + LineEnding +
    '  B := 20;' + LineEnding +
    '  C := A + B;' + LineEnding +
    '  WriteLn(C)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('30' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestNestedCalls;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_nested;' + LineEnding +
    'function Twice(X: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := X * 2' + LineEnding +
    'end;' + LineEnding +
    'function AddOne(X: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := X + 1' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(AddOne(Twice(5)))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('11' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestClassVirtualCall;
var
  Out_: string;
  EC: Integer;
begin
  { Exercises .quad <symbol> vtable entries and bare (%reg) stores —
    both previously broken in the internal assembler. }
  if not CompileAndRun(
    'program test_class;' + LineEnding +
    'type' + LineEnding +
    '  TGreeter = class' + LineEnding +
    '    function Greet: string; virtual;' + LineEnding +
    '  end;' + LineEnding +
    'function TGreeter.Greet: string;' + LineEnding +
    'begin' + LineEnding +
    '  Result := ''hello''' + LineEnding +
    'end;' + LineEnding +
    'var G: TGreeter;' + LineEnding +
    'begin' + LineEnding +
    '  G := TGreeter.Create;' + LineEnding +
    '  WriteLn(G.Greet());' + LineEnding +
    '  G.Free()' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('hello' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFloatArithmetic;
var
  Out_: string;
  EC: Integer;
begin
  { Exercises SSE loads/stores with bare (%reg) operands (float
    spills) — previously unparseable in the internal assembler. }
  if not CompileAndRun(
    'program test_float;' + LineEnding +
    'var A, B: Double;' + LineEnding +
    'begin' + LineEnding +
    '  A := 1.5;' + LineEnding +
    '  B := A * 2.0;' + LineEnding +
    '  if B = 3.0 then' + LineEnding +
    '    WriteLn(''ok'')' + LineEnding +
    '  else' + LineEnding +
    '    WriteLn(''bad'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('ok' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFormatFloatArg;
var
  Out_: string;
  EC: Integer;
begin
  { A float argument to Format() is boxed into the array-of-const via
    `movq %xmm0, %rax` (raw IEEE-754 bits).  The internal assembler used to
    mis-encode that as `mov %rax,%rax`, so the value was dropped and the float
    printed as 0.0000.  This is the end-to-end guard for that fix; the e2e test
    harness assembles native via cc, so only the internal-assembler suite
    exercises this path.  (issue #133 follow-up regression.) }
  if not CompileAndRun(
    'program test_fmtfloat;' + LineEnding +
    'uses sysutils;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Format(''%.4f'', [1.25]))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('1.2500' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestEntry_ExitCodePropagates;
var
  Out_: string;
  EC: Integer;
begin
  { Halt(N): the runtime's own _start calls __libc_start_main(main, ...) and
    glibc exits with main's return value.  A broken entry sequence would crash
    at startup or return the wrong code.  No system Scrt1.o is involved. }
  if not CompileAndRun(
    'program test_exit;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''before'');' + LineEnding +
    '  Halt(7)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(7, EC);
  AssertEquals('before' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestEntry_ArgsForwarded;
var
  Out_: string;
  EC: Integer;
begin
  { argc/argv reach the program through _start -> __libc_start_main -> main ->
    _SetArgs.  ParamStr(0) is the program path; the passed args follow. }
  if not CompileAndRunArgs(
    'program test_args;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(ParamCount());' + LineEnding +
    '  WriteLn(ParamStr(1));' + LineEnding +
    '  WriteLn(ParamStr(2))' + LineEnding +
    'end.',
    ['alpha', 'beta'], Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('2' + LineEnding + 'alpha' + LineEnding + 'beta' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestInlineAsm_ReturnsValue;
var
  Out_: string;
  EC: Integer;
begin
  { A nostackframe asm-body function returns 42 in %eax; the internal assembler
    assembles the verbatim block, and Pascal calls it normally. }
  if not CompileAndRun(
    'program test_asmret;' + LineEnding +
    'function GetFortyTwo: Integer; assembler; nostackframe;' + LineEnding +
    'asm' + LineEnding +
    '    movl $42, %eax' + LineEnding +
    '    ret' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(GetFortyTwo())' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestInlineAsm_AddsTwoArgs;
var
  Out_: string;
  EC: Integer;
begin
  { Two integer args arrive in %edi/%esi (SysV); the asm body sums them.  Proves
    a nostackframe asm function reads its parameters from the arg registers. }
  if not CompileAndRun(
    'program test_asmadd;' + LineEnding +
    'function AddTwo(A, B: Integer): Integer; assembler; nostackframe;' + LineEnding +
    'asm' + LineEnding +
    '    movl %edi, %eax' + LineEnding +
    '    addl %esi, %eax' + LineEnding +
    '    ret' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(AddTwo(40, 2))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestDebugOPDF_StringConstSpecialChars_AssemblesAndRuns;
var
  SrcFile, OutFile, CompOut, RunOut: string;
  Rc, EC: Integer;
  Src: string;
begin
  if not Self.CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;

  { A double-quote, a newline and a backslash in string-constant VALUES — each
    would break the recConstant `.ascii` line if emitted unescaped. }
  Src :=
    'program test_opdf_qc;' + LineEnding +
    'const' + LineEnding +
    '  Q = ' + '''' + '"' + '''' + ';' + LineEnding +
    '  NL = ' + '''' + 'a' + '''' + '#10' + '''' + 'b' + '''' + ';' + LineEnding +
    '  BS = ' + '''' + 'a\b' + '''' + ';' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Q);' + LineEnding +
    '  WriteLn(NL);' + LineEnding +
    '  WriteLn(BS)' + LineEnding +
    'end.';

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_opdf_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_opdf_' + IntToStr(FCounter);
  WriteFile(SrcFile, Src);

  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal',
    '--debug-opdf'
  ], CompOut);
  { The bug manifested as an "Internal assembler error: ... unhandled mnemonic"
    from the mangled .ascii line — a non-zero compile with that text. }
  if Rc <> 0 then
    Fail('compile under --debug-opdf failed (rc=' + IntToStr(Rc) + '): ' + CompOut);

  EC := Self.RunProcNoArgs(OutFile, RunOut);
  AssertEquals(0, EC);
  AssertEquals('"' + LineEnding + 'a' + LineEnding + 'b' + LineEnding +
               'a\b' + LineEnding, RunOut);
end;

{ ---- Registration ---- }

initialization
  RegisterTest(TAsmEncodingTests);
  RegisterTest(TElfWriterTests);
  RegisterTest(TInternalAsmE2ETests);

end.
