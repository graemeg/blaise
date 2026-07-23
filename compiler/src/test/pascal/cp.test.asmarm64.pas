{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.asmarm64;

{ Byte-level tests for the AArch64 internal assembler (macos-arm64
  Phase 1b).  Expected encodings are the architectural A64 words
  (cross-checked against the ARM ARM tables; behavioural confirmation
  happens on real Apple Silicon in Phase 6). }

interface

uses
  SysUtils, blaise.testing, uStrCompat, blaise.container.writer,
  blaise.machowriter, blaise.machoreader, blaise.assembler.arm64;

type
  TArm64AsmTests = class(TTestCase)
  private
    { Assemble one .text body and return the __text words. }
    function TextWords(const ABody: string; out AFile: TMachOFile): TMoSection;
    function WordAt(ASec: TMoSection; AIdx: Integer): Integer;
    procedure AssertWord(const AAsm: string; AExpected: Integer);
  published
    procedure TestNopRet;
    procedure TestAddSubSpRegisterUsesExtendedForm;
    procedure TestPrologueEpilogue_StpLdp;
    procedure TestAddSubImm;
    procedure TestAddSubCmpReg;
    procedure TestMovFamily;
    procedure TestMulDiv;
    procedure TestLogicAndShifts;
    procedure TestLoadsStores;
    procedure TestLoadStore_UnscaledAutoDowngrade;
    procedure TestFloatOps;
    procedure TestLocalBranches_ResolveToDeltas;
    procedure TestBlUndefined_EmitsBranch26;
    procedure TestAdrpAddPair_EmitsPageRelocs;
    procedure TestGotAndTlvRelocs;
    procedure TestDataDirectives_QuadSymbolReloc;
    procedure TestAsciiWithSemicolonAndSlashes;
    procedure TestCsetAndConditionals;
    procedure TestLseAtomics;
    procedure TestErrors_HaveLineNumbers;
  end;

implementation

function TArm64AsmTests.TextWords(const ABody: string;
  out AFile: TMachOFile): TMoSection;
begin
  AFile := ParseMachO(AssembleArm64ToBytes(ABody), 'arm64probe');
  Result := AFile.FindSection('__TEXT', '__text');
  AssertTrue('__text present', Result <> nil);
end;

function TArm64AsmTests.WordAt(ASec: TMoSection; AIdx: Integer): Integer;
begin
  Result := StrAt(ASec.Data, AIdx * 4)
    or (StrAt(ASec.Data, AIdx * 4 + 1) shl 8)
    or (StrAt(ASec.Data, AIdx * 4 + 2) shl 16)
    or (StrAt(ASec.Data, AIdx * 4 + 3) shl 24);
end;

procedure TArm64AsmTests.AssertWord(const AAsm: string; AExpected: Integer);
var
  F: TMachOFile;
  T: TMoSection;
begin
  T := TextWords(AAsm + LineEnding, F);
  try
    AssertEquals('encoding of "' + AAsm + '"', AExpected, WordAt(T, 0));
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestAddSubSpRegisterUsesExtendedForm;
begin
  { add/sub with a REGISTER third operand has two forms.  The shifted-register
    form (base $0B000000) decodes register 31 as XZR; only the EXTENDED form
    (base $0B200000, option UXTX) decodes it as SP.

    The assembler used the shifted form unconditionally, so the prologue's
    `sub sp, sp, x16` — the way a frame LARGER than the 4095-byte immediate
    limit is reserved — assembled as `sub xzr, xzr, x16`: a no-op.  Every
    function with a frame over 4095 bytes therefore never reserved its stack,
    leaving its locals below sp to be overwritten by the next callee's
    prologue push (macOS arm64, 2026-07-23).  Small frames use the immediate
    form, which encodes 31 as sp correctly, which is why only large-frame
    functions were affected.

    0xCB3063FF = sub sp, sp, x16, uxtx #0   (correct)
    0xCB1003FF = sub xzr, xzr, x16          (the no-op it used to emit) }
  AssertWord('sub sp, sp, x16', Integer($CB3063FF));
  AssertWord('add sp, sp, x16', Integer($8B3063FF));
  { a non-sp register operand keeps the shifted form }
  AssertWord('sub x0, x1, x2', Integer($CB020020));
end;

procedure TArm64AsmTests.TestNopRet;
begin
  AssertWord('nop', Integer($D503201F));
  AssertWord('ret', Integer($D65F03C0));
  AssertWord('brk #0', Integer($D4200000));
end;

procedure TArm64AsmTests.TestPrologueEpilogue_StpLdp;
begin
  { the canonical frame save/restore pair }
  AssertWord('stp x29, x30, [sp, #-16]!', Integer($A9BF7BFD));
  AssertWord('ldp x29, x30, [sp], #16', Integer($A8C17BFD));
  AssertWord('stp x19, x20, [sp, #16]', Integer($A90153F3));
  AssertWord('mov x29, sp', Integer($910003FD));
end;

procedure TArm64AsmTests.TestAddSubImm;
begin
  AssertWord('add x0, x1, #4', Integer($91001020));
  AssertWord('sub sp, sp, #32', Integer($D10083FF));
  AssertWord('subs w0, w1, #1', Integer($71000420));
  AssertWord('cmp w0, #0', Integer($7100001F));
end;

procedure TArm64AsmTests.TestAddSubCmpReg;
begin
  AssertWord('add x0, x1, x2', Integer($8B020020));
  AssertWord('sub w3, w4, w5', Integer($4B050083));
  AssertWord('cmp x1, x2', Integer($EB02003F));
  AssertWord('neg x0, x1', Integer($CB0103E0));
end;

procedure TArm64AsmTests.TestMovFamily;
begin
  AssertWord('movz w0, #5', Integer($528000A0));
  AssertWord('movk x0, #1, lsl #16', Integer($F2A00020));
  AssertWord('mov x1, x2', Integer($AA0203E1));
  AssertWord('mov w0, #7', Integer($528000E0));
  AssertWord('mov x0, #-1', Integer($92800000));
end;

procedure TArm64AsmTests.TestMulDiv;
begin
  AssertWord('mul x0, x1, x2', Integer($9B027C20));
  AssertWord('sdiv x0, x1, x2', Integer($9AC20C20));
  AssertWord('udiv w0, w1, w2', Integer($1AC20820));
  AssertWord('msub x0, x1, x2, x3', Integer($9B028C20));
end;

procedure TArm64AsmTests.TestLogicAndShifts;
begin
  AssertWord('and x0, x1, x2', Integer($8A020020));
  AssertWord('orr x0, x1, x2', Integer($AA020020));
  AssertWord('eor w0, w1, w2', Integer($4A020020));
  AssertWord('lsl x0, x1, x2', Integer($9AC22020));
  AssertWord('lsr x0, x1, #3', Integer($D343FC20));
  AssertWord('lsl x0, x1, #4', Integer($D37CEC20));
  AssertWord('asr w0, w1, #1', Integer($13017C20));
  AssertWord('sxtw x0, w0', Integer($93407C00));
end;

procedure TArm64AsmTests.TestLoadsStores;
begin
  AssertWord('ldr x0, [x1, #8]', Integer($F9400420));
  AssertWord('str x0, [sp]', Integer($F90003E0));
  AssertWord('ldr w2, [x3, #4]', Integer($B9400462));
  AssertWord('ldrb w0, [x1]', Integer($39400020));
  AssertWord('strb w0, [x1, #1]', Integer($39000420));
  AssertWord('ldrh w0, [x1]', Integer($79400020));
  AssertWord('ldrsw x0, [x1]', Integer($B9800020));
  AssertWord('ldur x0, [x1, #-8]', Integer($F85F8020));
  { single-register pre/post-index — the backend's stack brackets }
  AssertWord('str x0, [sp, #-16]!', Integer($F81F0FE0));
  AssertWord('ldr x9, [sp], #16', Integer($F84107E9));
  AssertWord('ldr d0, [x1, #8]', Integer($FD400420));
  AssertWord('str d0, [sp]', Integer($FD0003E0));
end;

procedure TArm64AsmTests.TestLoadStore_UnscaledAutoDowngrade;
var
  F: TMachOFile;
  T: TMoSection;
  UrWord: Integer;
begin
  { A plain ldr/str whose offset is not a multiple of the access size, or is
    negative, cannot use the scaled 12-bit form but IS a valid unscaled
    ldur/stur in [-256..255].  GNU as auto-selects ldur/stur there; the internal
    assembler now does too — so `ldr x0, [x1, #20]` assembles identically to
    `ldur x0, [x1, #20]` instead of raising.  (Exposed by the arm64 self-compile
    of the whole compiler, which emits such loads.) }
  T := TextWords('ldur x0, [x1, #20]' + LineEnding, F);
  try UrWord := WordAt(T, 0); finally F.Free(); end;
  AssertWord('ldr x0, [x1, #20]', UrWord);

  T := TextWords('stur x0, [x1, #-4]' + LineEnding, F);
  try UrWord := WordAt(T, 0); finally F.Free(); end;
  AssertWord('str x0, [x1, #-4]', UrWord);

  T := TextWords('ldur w2, [x3, #3]' + LineEnding, F);
  try UrWord := WordAt(T, 0); finally F.Free(); end;
  AssertWord('ldr w2, [x3, #3]', UrWord);
end;

procedure TArm64AsmTests.TestFloatOps;
begin
  AssertWord('fadd d0, d1, d2', Integer($1E622820));
  AssertWord('fsub d0, d1, d2', Integer($1E623820));
  AssertWord('fmul d0, d1, d2', Integer($1E620820));
  AssertWord('fdiv d0, d1, d2', Integer($1E621820));
  AssertWord('fcmp d0, d1', Integer($1E612000));
  AssertWord('fcmp d0, #0.0', Integer($1E602008));
  AssertWord('scvtf d0, x1', Integer($9E620020));
  AssertWord('fcvtzs x0, d1', Integer($9E780020));
  AssertWord('fmov d0, x1', Integer($9E670020));
  AssertWord('fmov x0, d1', Integer($9E660020));
  AssertWord('fmov d0, d1', Integer($1E604020));
  { precision conversions + 32-bit fp load/store (Single support) }
  AssertWord('fcvt d0, s1', Integer($1E22C020));
  AssertWord('fcvt s2, d3', Integer($1E624062));
  AssertWord('ldr s0, [x9, #8]', Integer($BD400920));
  AssertWord('str s1, [x9, #4]', Integer($BD000521));
  { fp pre/post-index — the backend's float stack brackets }
  AssertWord('str d0, [sp, #-16]!', Integer($FC1F0FE0));
  AssertWord('ldr d0, [sp], #16', Integer($FC4107E0));
end;

procedure TArm64AsmTests.TestLocalBranches_ResolveToDeltas;
var
  F: TMachOFile;
  T: TMoSection;
begin
  T := TextWords(
    'top:' + LineEnding +
    'nop' + LineEnding +
    'b top' + LineEnding +          { delta -4 -> imm26 = -1 }
    'cbz x0, top' + LineEnding +    { delta -8 -> imm19 = -2 }
    'b.eq top' + LineEnding, F);
  try
    AssertEquals('b back by one word',
      Integer($17FFFFFF), WordAt(T, 1));
    AssertEquals('cbz back by two words',
      Integer($B4FFFFC0), WordAt(T, 2));
    AssertEquals('b.eq back by three words',
      Integer($54FFFFA0), WordAt(T, 3));
    AssertEquals('no relocations for local branches', 0, T.Relocs.Count);
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestBlUndefined_EmitsBranch26;
var
  F: TMachOFile;
  T: TMoSection;
begin
  T := TextWords('bl _puts' + LineEnding, F);
  try
    AssertEquals(Integer($94000000), WordAt(T, 0));
    AssertEquals(1, T.Relocs.Count);
    AssertEquals(ARM64_RELOC_BRANCH26, T.Relocs.Get(0).RType);
    AssertTrue(T.Relocs.Get(0).PcRel);
    AssertEquals('_puts',
      F.Symbols.Get(T.Relocs.Get(0).SymbolNum).Name);
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestAdrpAddPair_EmitsPageRelocs;
var
  F: TMachOFile;
  T: TMoSection;
begin
  T := TextWords(
    'adrp x0, _gvar@PAGE' + LineEnding +
    'add x0, x0, _gvar@PAGEOFF' + LineEnding +
    'ldr x1, [x0, _gvar@PAGEOFF]' + LineEnding +
    '.data' + LineEnding +
    '_gvar:' + LineEnding +
    '.quad 42' + LineEnding, F);
  try
    AssertEquals(3, T.Relocs.Count);
    AssertEquals(ARM64_RELOC_PAGE21, T.Relocs.Get(0).RType);
    AssertTrue('page21 pc-relative', T.Relocs.Get(0).PcRel);
    AssertEquals(ARM64_RELOC_PAGEOFF12, T.Relocs.Get(1).RType);
    AssertEquals(ARM64_RELOC_PAGEOFF12, T.Relocs.Get(2).RType);
    { the target is the DEFINED local _gvar, not a minted extern }
    AssertTrue('_gvar defined in __data',
      not F.Symbols.Get(T.Relocs.Get(0).SymbolNum).IsUndef());
    AssertEquals('adrp word', Integer($90000000), WordAt(T, 0));
    AssertEquals('add-pageoff word', Integer($91000000), WordAt(T, 1));
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestGotAndTlvRelocs;
var
  F: TMachOFile;
  T: TMoSection;
begin
  T := TextWords(
    'adrp x0, _ext@GOTPAGE' + LineEnding +
    'ldr x0, [x0, _ext@GOTPAGEOFF]' + LineEnding +
    'adrp x1, _tv@TLVPPAGE' + LineEnding +
    'ldr x1, [x1, _tv@TLVPPAGEOFF]' + LineEnding, F);
  try
    AssertEquals(4, T.Relocs.Count);
    AssertEquals(ARM64_RELOC_GOT_LOAD_PAGE21, T.Relocs.Get(0).RType);
    AssertEquals(ARM64_RELOC_GOT_LOAD_PAGEOFF12, T.Relocs.Get(1).RType);
    AssertEquals(ARM64_RELOC_TLVP_LOAD_PAGE21, T.Relocs.Get(2).RType);
    AssertEquals(ARM64_RELOC_TLVP_LOAD_PAGEOFF12, T.Relocs.Get(3).RType);
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestDataDirectives_QuadSymbolReloc;
var
  F: TMachOFile;
  D: TMoSection;
begin
  TextWords(
    'nop' + LineEnding +
    '.data' + LineEnding +
    '.balign 8' + LineEnding +
    'ptr:' + LineEnding +
    '.quad _target' + LineEnding +
    '.word 7' + LineEnding +
    '.byte 1, 2' + LineEnding +
    '.asciz "hi"' + LineEnding, F);
  try
    D := F.FindSection('__DATA', '__data');
    AssertTrue(D <> nil);
    AssertEquals('quad slot + word + 2 bytes + "hi\0"',
      8 + 4 + 2 + 3, Integer(D.Size));
    AssertEquals(1, D.Relocs.Count);
    AssertEquals(ARM64_RELOC_UNSIGNED, D.Relocs.Get(0).RType);
    AssertEquals('8-byte width', 3, D.Relocs.Get(0).Length_);
    AssertEquals(7, StrAt(D.Data, 8));
    AssertEquals(Ord('h'), StrAt(D.Data, 14));
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestAsciiWithSemicolonAndSlashes;
var
  F: TMachOFile;
  D: TMoSection;
begin
  { The line comment-stripper must NOT treat ';' or '//' as a comment when they
    sit INSIDE a quoted string — else `.ascii ";"` loses its byte and becomes an
    unterminated `.ascii "`.  (Exposed by the arm64 self-compile, whose emitted
    string constants include semicolons and '//'.) }
  TextWords(
    'nop' + LineEnding +
    '.data' + LineEnding +
    'lbl:' + LineEnding +
    '.ascii ";"' + LineEnding +
    '.ascii "a//b"' + LineEnding, F);
  try
    D := F.FindSection('__DATA', '__data');
    AssertTrue(D <> nil);
    { one ';' byte + four bytes 'a//b' }
    AssertEquals('";" + "a//b"', 1 + 4, Integer(D.Size));
    AssertEquals('semicolon preserved', Ord(';'), StrAt(D.Data, 0));
    AssertEquals('a', Ord('a'), StrAt(D.Data, 1));
    AssertEquals('first slash preserved', Ord('/'), StrAt(D.Data, 2));
    AssertEquals('second slash preserved', Ord('/'), StrAt(D.Data, 3));
    AssertEquals('b', Ord('b'), StrAt(D.Data, 4));
  finally
    F.Free();
  end;
end;

procedure TArm64AsmTests.TestCsetAndConditionals;
begin
  { cset w0, eq  ->  csinc w0, wzr, wzr, ne }
  AssertWord('cset w0, eq', Integer($1A9F17E0));
  AssertWord('cset x0, lt', Integer($9A9FA7E0));
end;

procedure TArm64AsmTests.TestLseAtomics;
begin
  { LSE atomics for runtime.atomic.arm64 (acquire+release variants only —
    that is what ARC and the allocator's remote-free queue need).
    Reference encodings cross-checked against GNU as. }
  AssertWord('ldaddal w1, w2, [x0]', Integer($B8E10002));
  AssertWord('ldaddal x1, x9, [x0]', Integer($F8E10009));
  AssertWord('swpal x1, x9, [x0]', Integer($F8E18009));
  AssertWord('swpal w1, w2, [x0]', Integer($B8E18002));
  AssertWord('casal x1, x2, [x0]', Integer($C8E1FC02));
  AssertWord('casal w1, w2, [x0]', Integer($88E1FC02));
end;

procedure TArm64AsmTests.TestErrors_HaveLineNumbers;
var
  Raised: Boolean;
  Msg: string;
begin
  Raised := False;
  Msg := '';
  try
    AssembleArm64ToBytes('nop' + LineEnding + 'frobnicate x0' + LineEnding);
  except
    on E: EArm64Assembler do
    begin
      Raised := True;
      Msg := E.Message;
    end;
  end;
  AssertTrue('unknown mnemonic raises', Raised);
  AssertTrue('message names line 2', Pos('line 2', Msg) >= 0);
end;

initialization
  RegisterTest(TArm64AsmTests);

end.
