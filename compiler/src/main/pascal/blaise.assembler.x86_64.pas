{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.assembler.x86_64;

{ Self-assembler for the native x86-64 backend's AT&T assembly dialect.

  Route A of the toolchain-independence plan: parses the restricted AT&T
  subset the native backend emits — a closed set of ~90 mnemonics,
  operand shapes, directives, and label forms — and encodes it into a
  relocatable object file.  The object is built through the
  IContainerWriter seam (blaise.container.writer); the concrete writer
  today is TElfObjectWriter (blaise.elfwriter).

  The codegen unit is untouched; the textual .s remains the canonical
  artefact.  The self-assembler is an alternative to shelling out to
  GNU as for the assembly step.

  Two-pass assembly:
    Pass 1 — collect labels, compute section sizes (instruction sizes
             are fixed or conservatively estimated, then shrunk).
    Pass 2 — encode instructions with resolved label offsets, emitting
             relocations for external symbols. }

interface

uses
  SysUtils, Generics.Collections, blaise.container.writer, blaise.elfwriter;

type
  EAssembler = class(Exception);

  TLabelInfo = record
    Section: TContainerSectionKind;
    Offset:  Integer;
    Defined: Boolean;
  end;

  TLabelMap = class
  private
    FIndex: TDictionary<string, Integer>;
    FKeys:  array of string;
    FVals:  array of TLabelInfo;
    FCount: Integer;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Add(const AKey: string; AVal: TLabelInfo);
    procedure Remove(const AKey: string);
    function ContainsKey(const AKey: string): Boolean;
    function TryGetValue(const AKey: string; var AVal: TLabelInfo): Boolean;
    function GetKey(AIdx: Integer): string;
    function GetVal(AIdx: Integer): TLabelInfo;
    property Count: Integer read FCount;
  end;

procedure AssembleToObject(const AAsmText: string; const AOutputPath: string);

function AssembleToBytes(const AAsmText: string): string;

implementation

{ ---- Float helpers ----------------------------------------------------- }

function _StrToDouble(S: Pointer): Double; external name '_StrToDouble';

function DoubleBits(V: Double): Int64;
var
  P: ^Int64;
begin
  P := Pointer(@V);
  Result := P^;
end;

function SingleBits(V: Single): Integer;
var
  P: ^Integer;
begin
  P := Pointer(@V);
  Result := P^;
end;

{ ---- Register encoding ------------------------------------------------ }

const
  REG_COUNT = 66;

  RegNames: array[0..99] of string = (
    'rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
    'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15',
    'eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi',
    'r8d', 'r9d', 'r10d', 'r11d', 'r12d', 'r13d', 'r14d', 'r15d',
    'ax', 'cx', 'dx', 'bx', 'sp', 'bp', 'si', 'di', 'r8w', 'r9w',
    'al', 'cl', 'dl', 'bl', 'spl', 'bpl', 'sil', 'dil',
    'r8b', 'r9b', 'r10b', 'r11b',
    'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5', 'xmm6', 'xmm7',
    'ah', 'ch', 'dh', 'bh',
    'xmm8', 'xmm9', 'xmm10', 'xmm11', 'xmm12', 'xmm13', 'xmm14', 'xmm15',
    'ymm0', 'ymm1', 'ymm2', 'ymm3', 'ymm4', 'ymm5', 'ymm6', 'ymm7',
    'ymm8', 'ymm9', 'ymm10', 'ymm11', 'ymm12', 'ymm13', 'ymm14', 'ymm15',
    'r10w', 'r11w', 'r12w', 'r13w', 'r14w', 'r15w',
    'r12b', 'r13b', 'r14b', 'r15b'
  );

  RegCodes: array[0..99] of Integer = (
    0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11,
    0, 1, 2, 3, 4, 5, 6, 7,
    4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    10, 11, 12, 13, 14, 15,
    12, 13, 14, 15
  );

  RegWidths: array[0..99] of Integer = (
    64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64,
    32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32, 32, 32,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8,
    128, 128, 128, 128, 128, 128, 128, 128,
    8, 8, 8, 8,
    128, 128, 128, 128, 128, 128, 128, 128,
    256, 256, 256, 256, 256, 256, 256, 256,
    256, 256, 256, 256, 256, 256, 256, 256,
    16, 16, 16, 16, 16, 16,
    8, 8, 8, 8
  );

  RegIsXmm: array[0..99] of Integer = (
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0, 0, 0,
    0, 0, 0, 0
  );

type
  { Parsed operand types }
  TOperandKind = (
    opNone,
    opReg,          { %rax, %eax, %al, %xmm0 etc. }
    opImm,          { $42, $-1, $0x1F }
    opImm64,        { 64-bit immediate (for movabsq) }
    opMem,          { disp(%base), (%base), disp(%base,%index,scale) }
    opRipRel,       { sym(%rip), sym+disp(%rip) }
    opLabel,        { .Lxxx or bare symbol (branch targets) }
    opIndirect,     { *%rax (indirect call/jmp) }
    opTLS           { %fs:sym@tpoff }
  );

  TOperand = record
    Kind:    TOperandKind;
    Reg:     Integer;      { register code (0-15) }
    RegW:    Integer;      { register width }
    IsXmm:  Boolean;
    Imm:     Int64;        { immediate value }
    Disp:    Int64;        { memory displacement }
    Base:    Integer;      { base register code (-1 = none) }
    Index:   Integer;      { index register code (-1 = none) }
    Scale:   Integer;      { 1, 2, 4, or 8 }
    Sym:     string;       { symbol name (for RIP-rel, labels, TLS) }
    SymDisp: Int64;        { addend to symbol (sym + N) }
    TpOff:   Boolean;      { sym@tpoff — emit R_X86_64_TPOFF32 relocation }
    Indirect: Boolean;     { memory operand reached via *mem (call/jmp *disp(%reg)) }
  end;

  { Parsed line types }
  TLineKind = (
    lkEmpty,
    lkLabel,
    lkInstr,
    lkDirective
  );

  TParsedLine = record
    Kind:      TLineKind;
    Mnemonic:  string;     { instruction mnemonic or directive name }
    Op1, Op2, Op3: TOperand; { up to three operands (Op3 for VEX/imm forms) }
    NumOps:    Integer;
    RawLine:   string;     { original line text }
    LineNum:   Integer;
    HasLock:   Boolean;    { a `lock` prefix preceded the mnemonic }
  end;

  { Internal assembler state for a single section }
  TSectionState = record
    Kind:   TContainerSectionKind;
    Offset: Integer;       { current offset within section }
  end;


{ ---- String helpers --------------------------------------------------- }

function IsDigit(C: Integer): Boolean;
begin
  Result := (C >= Ord('0')) and (C <= Ord('9'));
end;

function IsAlpha(C: Integer): Boolean;
begin
  Result := ((C >= Ord('a')) and (C <= Ord('z'))) or
            ((C >= Ord('A')) and (C <= Ord('Z'))) or (C = Ord('_'));
end;

function IsAlnum(C: Integer): Boolean;
begin
  Result := IsDigit(C) or IsAlpha(C);
end;

function IsHexDigit(C: Integer): Boolean;
begin
  Result := IsDigit(C) or ((C >= Ord('a')) and (C <= Ord('f'))) or
            ((C >= Ord('A')) and (C <= Ord('F')));
end;

function TrimStr(const S: string): string;
var
  Lo, Hi: Integer;
begin
  Lo := 0;
  Hi := Length(S) - 1;
  while (Lo <= Hi) and ((S[Lo]= Ord(' ')) or (S[Lo]= 9) or (S[Lo]= 13)) do
    Lo := Lo + 1;
  while (Hi >= Lo) and ((S[Hi]= Ord(' ')) or (S[Hi]= 9) or (S[Hi]= 13)) do
    Hi := Hi - 1;
  if Lo > Hi then
    Result := ''
  else
    Result := Copy(S, Lo, Hi - Lo + 1);
end;

function StartsWithStr(const S, Prefix: string): Boolean;
var
  I: Integer;
begin
  if Length(Prefix) > Length(S) then
  begin
    Result := False;
    Exit;
  end;
  I := 0;
  while I < Length(Prefix) do
  begin
    if S[I] <> Prefix[I] then
    begin
      Result := False;
      Exit;
    end;
    I := I + 1;
  end;
  Result := True;
end;

function ParseInt(const S: string; var APos: Integer): Int64;
var
  Neg: Boolean;
  Base: Integer;
  C: Integer;
  Digit: Integer;
begin
  Result := 0;
  Neg := False;
  if (APos < Length(S)) and (S[APos]= Ord('-')) then
  begin
    Neg := True;
    APos := APos + 1;
  end;
  Base := 10;
  if (APos + 1 < Length(S)) and (S[APos]= Ord('0')) and (S[APos + 1]= Ord('x')) then
  begin
    Base := 16;
    APos := APos + 2;
  end;
  while APos < Length(S) do
  begin
    C := S[APos];
    if Base = 16 then
    begin
      if not IsHexDigit(C) then break;
      if IsDigit(C) then
        Digit := Ord(C) - Ord('0')
      else if (C >= Ord('a')) and (C <= Ord('f')) then
        Digit := 10 + Ord(C) - Ord('a')
      else
        Digit := 10 + Ord(C) - Ord('A');
    end
    else
    begin
      if not IsDigit(C) then break;
      Digit := Ord(C) - Ord('0');
    end;
    Result := Result * Base + Digit;
    APos := APos + 1;
  end;
  if Neg then Result := -Result;
end;

{ ---- Register lookup -------------------------------------------------- }

function LookupReg(const AName: string; var ACode: Integer;
  var AWidth: Integer; var AIsXmm: Boolean): Boolean;
var
  I: Integer;
begin
  I := 0;
  while I <= High(RegNames) do
  begin
    if RegNames[I] = AName then
    begin
      ACode  := RegCodes[I];
      AWidth := RegWidths[I];
      AIsXmm := RegIsXmm[I] <> 0;
      Result := True;
      Exit;
    end;
    I := I + 1;
  end;
  Result := False;
end;

{ ---- Operand parser --------------------------------------------------- }

function ParseOperand(const S: string; APos: Integer;
  var AEnd: Integer): TOperand;
var
  P: Integer;
  RegName: string;
  SymName: string;
  SymDisp: Int64;
  IdxW: Integer;
  IdxXmm: Boolean;
begin
  Result.Kind   := opNone;
  Result.Reg    := -1;
  Result.RegW   := 0;
  Result.IsXmm  := False;
  Result.Imm    := 0;
  Result.Disp   := 0;
  Result.Base   := -1;
  Result.Index  := -1;
  Result.Scale  := 1;
  Result.Sym    := '';
  Result.SymDisp := 0;
  Result.Indirect := False;

  P := APos;
  while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
    P := P + 1;

  if P >= Length(S) then
  begin
    AEnd := P;
    Exit;
  end;

  { Indirect operand: *%reg (register-indirect) or *disp(%reg) (memory-
    indirect), used by `call`/`jmp` through a pointer. }
  if S[P]= Ord('*') then
  begin
    P := P + 1;
    if (P < Length(S)) and (S[P]= Ord('%')) then
    begin
      P := P + 1;
      RegName := '';
      while (P < Length(S)) and (IsAlnum(S[P])) do
      begin
        RegName := RegName + Chr(S[P]);
        P := P + 1;
      end;
      Result.Kind := opIndirect;
      LookupReg(RegName, Result.Reg, Result.RegW, Result.IsXmm);
      AEnd := P;
      Exit;
    end;
    { *disp(%reg): parse the remainder as an ordinary memory operand and flag
      it indirect so the branch encoder uses FF /4 with that memory ModRM. }
    Result := ParseOperand(S, P, AEnd);
    Result.Indirect := True;
    Exit;
  end;

  { Immediate: $N }
  if S[P]= Ord('$') then
  begin
    P := P + 1;
    Result.Kind := opImm;
    Result.Imm := ParseInt(S, P);
    AEnd := P;
    Exit;
  end;

  { Register: %reg }
  if S[P]= Ord('%') then
  begin
    { Check for TLS: %fs:sym@tpoff or %fs:disp (numeric) }
    if (P + 2 < Length(S)) and (S[P + 1]= Ord('f')) and (S[P + 2]= Ord('s')) then
    begin
      if (P + 3 < Length(S)) and (S[P + 3]= Ord(':')) then
      begin
        P := P + 4;
        if (P < Length(S)) and (IsDigit(S[P]) or (S[P]= Ord('-'))) then
        begin
          Result.Kind := opTLS;
          Result.Sym := '';
          Result.Disp := ParseInt(S, P);
          AEnd := P;
          Exit;
        end;
        SymName := '';
        while (P < Length(S)) and (S[P]<> Ord('@')) and (S[P]<> Ord(' '))
              and (S[P]<> Ord(',')) and (S[P]<> 9) do
        begin
          SymName := SymName + Chr(S[P]);
          P := P + 1;
        end;
        if (P < Length(S)) and (S[P]= Ord('@')) then
        begin
          while (P < Length(S)) and (S[P]<> Ord(' ')) and (S[P]<> Ord(',')) and (S[P]<> 9) do
            P := P + 1;
        end;
        Result.Kind := opTLS;
        Result.Sym := SymName;
        AEnd := P;
        Exit;
      end;
    end;

    P := P + 1;
    RegName := '';
    while (P < Length(S)) and (IsAlnum(S[P])) do
    begin
      RegName := RegName + Chr(S[P]);
      P := P + 1;
    end;
    Result.Kind := opReg;
    if not LookupReg(RegName, Result.Reg, Result.RegW, Result.IsXmm) then
      raise EAssembler.Create('unknown register: %' + RegName);
    AEnd := P;
    Exit;
  end;

  { Memory or RIP-relative or label/symbol reference.
    Forms:
      disp(%base)
      disp(%base,%index,scale)
      (%base)
      sym(%rip)
      sym+disp(%rip)
      sym (bare label for branches)
      .Lxxx (local label)
  }
  SymName := '';
  SymDisp := 0;

  if (S[P]= Ord('-')) or IsDigit(S[P]) or (S[P]= Ord('(')) then
  begin
    { Numeric displacement (possibly zero/absent for bare (%base)),
      possibly followed by (%base) }
    if S[P]<> Ord('(') then
      Result.Disp := ParseInt(S, P);
    if (P < Length(S)) and (S[P]= Ord('(')) then
    begin
      { Memory operand: disp(%base,...) }
      P := P + 1;
      if (P < Length(S)) and (S[P]= Ord('%')) then
      begin
        P := P + 1;
        RegName := '';
        while (P < Length(S)) and (IsAlnum(S[P])) do
        begin
          RegName := RegName + Chr(S[P]);
          P := P + 1;
        end;
        LookupReg(RegName, Result.Base, Result.RegW, Result.IsXmm);
        if RegName = 'rip' then
        begin
          Result.Kind := opRipRel;
          Result.Sym := '';
          Result.SymDisp := Result.Disp;
          Result.Disp := 0;
        end
        else
          Result.Kind := opMem;
        { Check for index,scale.  GNU as allows whitespace after the commas,
          e.g. `(%rdi, %rdx)` and `(%rdi, %rdx, 4)`. }
        if (P < Length(S)) and (S[P]= Ord(',')) then
        begin
          P := P + 1;
          while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do P := P + 1;
          if (P < Length(S)) and (S[P]= Ord('%')) then
          begin
            P := P + 1;
            RegName := '';
            while (P < Length(S)) and (IsAlnum(S[P])) do
            begin
              RegName := RegName + Chr(S[P]);
              P := P + 1;
            end;
            LookupReg(RegName, Result.Index, IdxW, IdxXmm);
          end;
          while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do P := P + 1;
          if (P < Length(S)) and (S[P]= Ord(',')) then
          begin
            P := P + 1;
            while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do P := P + 1;
            Result.Scale := Integer(ParseInt(S, P));
          end;
        end;
        if (P < Length(S)) and (S[P]= Ord(')')) then
          P := P + 1;
      end;
      AEnd := P;
      Exit;
    end
    else
    begin
      { Bare number — treat as immediate for push etc. }
      Result.Kind := opImm;
      Result.Imm := Result.Disp;
      Result.Disp := 0;
      AEnd := P;
      Exit;
    end;
  end;

  { Symbol/label, possibly followed by @tpoff, +disp and/or (%rip) }
  if IsAlpha(S[P]) or (S[P]= Ord('.')) or (S[P]= Ord('_')) then
  begin
    while (P < Length(S)) and (IsAlnum(S[P]) or (S[P]= Ord('.')) or (S[P]= Ord('_'))
           or (S[P]= Ord('$'))) do
    begin
      SymName := SymName + Chr(S[P]);
      P := P + 1;
    end;
    if (P < Length(S)) and (S[P]= Ord('@')) then
    begin
      if (P + 5 <= Length(S))
         and (S[P + 1]= Ord('t')) and (S[P + 2]= Ord('p'))
         and (S[P + 3]= Ord('o')) and (S[P + 4]= Ord('f'))
         and (S[P + 5]= Ord('f'))
         and ((P + 6 >= Length(S)) or not IsAlnum(S[P + 6])) then
      begin
        Result.TpOff := True;
        P := P + 6;
      end
      else
      begin
        { Any other @SUFFIX (e.g. @PLT, @GOTPCREL) is a relocation qualifier,
          NOT part of the symbol name — consume and discard it.  @PLT just
          selects the PLT32 relocation, which call/jmp already emit by default.
          Appending it to the name would create a bogus symbol like
          `__libc_start_main@PLT` that no loader resolves. }
        P := P + 1;
        while (P < Length(S)) and (IsAlnum(S[P]) or (S[P]= Ord('_'))) do
          P := P + 1;
      end;
    end;

    { Skip whitespace before +/- displacement }
    while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
      P := P + 1;

    { Check for +disp or - disp after symbol }
    if (P < Length(S)) and ((S[P]= Ord('+')) or (S[P]= Ord('-'))) then
    begin
      if S[P]= Ord('+') then
      begin
        P := P + 1;
        while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
          P := P + 1;
        SymDisp := ParseInt(S, P);
      end
      else
      begin
        SymDisp := ParseInt(S, P);
      end;
    end;

    { Skip whitespace before (%rip) }
    while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
      P := P + 1;

    { Check for (%rip) }
    if (P < Length(S)) and (S[P]= Ord('(')) then
    begin
      P := P + 1;
      if (P < Length(S)) and (S[P]= Ord('%')) then
      begin
        P := P + 1;
        RegName := '';
        while (P < Length(S)) and (IsAlnum(S[P])) do
        begin
          RegName := RegName + Chr(S[P]);
          P := P + 1;
        end;
        if RegName = 'rip' then
        begin
          Result.Kind := opRipRel;
          Result.Sym := SymName;
          Result.SymDisp := SymDisp;
          if (P < Length(S)) and (S[P]= Ord(')')) then
            P := P + 1;
          AEnd := P;
          Exit;
        end
        else
        begin
          { sym(%base) — symbol used as displacement }
          Result.Kind := opMem;
          Result.Sym := SymName;
          Result.SymDisp := SymDisp;
          LookupReg(RegName, Result.Base, Result.RegW, Result.IsXmm);
          if (P < Length(S)) and (S[P]= Ord(')')) then
            P := P + 1;
          AEnd := P;
          Exit;
        end;
      end;
      if (P < Length(S)) and (S[P]= Ord(')')) then
        P := P + 1;
    end;

    { Bare symbol — branch target or data reference }
    Result.Kind := opLabel;
    Result.Sym := SymName;
    Result.SymDisp := SymDisp;
    AEnd := P;
    Exit;
  end;

  AEnd := P;
end;

{ ---- Line parser ------------------------------------------------------ }

function ParseLine(const ALine: string; ALineNum: Integer): TParsedLine;
var
  S: string;
  P, Q, OpEnd: Integer;
  Mnemonic: string;
  TmpOp: TOperand;
begin
  Result.Kind := lkEmpty;
  Result.Mnemonic := '';
  Result.NumOps := 0;
  Result.RawLine := ALine;
  Result.LineNum := ALineNum;
  Result.HasLock := False;
  Result.Op1.Kind := opNone;
  Result.Op2.Kind := opNone;
  Result.Op3.Kind := opNone;

  S := TrimStr(ALine);
  if (Length(S) = 0) or (S[0]= Ord('#')) then Exit;

  { Strip a brace comment (open/close = ASCII 123/125) that survived the lexer:
    a whole-line or trailing comment inside an asm block.  Single line only;
    remove the span from the open brace to the matching close brace, or to end
    of line when unterminated.  Skip over quoted strings so that a brace INSIDE
    a .ascii string literal (the string-const data the native backend emits) is
    left intact rather than mistaken for a comment. }
  P := 0;
  while P < Length(S) do
  begin
    if S[P] = Ord('"') then
    begin
      { Skip the whole quoted string, honouring \" escapes. }
      P := P + 1;
      while P < Length(S) do
      begin
        if S[P] = Ord('\') then
          P := P + 2
        else if S[P] = Ord('"') then
        begin
          P := P + 1;
          Break;
        end
        else
          P := P + 1;
      end;
    end
    else if S[P] = 123 then
    begin
      Q := P + 1;
      while (Q < Length(S)) and (S[Q] <> 125) do
        Q := Q + 1;
      { Splice out [P..Q] WITHOUT trimming mid-scan (a left-trim would shift the
        string under P); resume from P so a following brace is still found. }
      if Q < Length(S) then
        S := Copy(S, 0, P) + ' ' + Copy(S, Q + 1, Length(S))
      else
        S := Copy(S, 0, P);
    end
    else
      P := P + 1;
  end;
  S := TrimStr(S);
  if Length(S) = 0 then Exit;

  { Strip trailing comment, but skip over quoted strings so that '#'
    inside .ascii "..." is not mistaken for a comment start. }
  P := 0;
  while P < Length(S) do
  begin
    if S[P] = Ord('"') then
    begin
      P := P + 1;
      while P < Length(S) do
      begin
        if S[P] = Ord('\') then
          P := P + 2
        else if S[P] = Ord('"') then
        begin
          P := P + 1;
          break;
        end
        else
          P := P + 1;
      end;
    end
    else if S[P] = Ord('#') then
    begin
      S := Copy(S, 0, P);
      S := TrimStr(S);
      break;
    end
    else
      P := P + 1;
  end;
  if Length(S) = 0 then Exit;

  { Label: ends with ':' }
  if (Length(S) > 1) and (S[Length(S) - 1]= Ord(':')) then
  begin
    Result.Kind := lkLabel;
    Result.Mnemonic := Copy(S, 0, Length(S) - 1);
    Exit;
  end;

  { Directive: starts with '.' }
  if S[0]= Ord('.') then
  begin
    Result.Kind := lkDirective;
    P := 1;
    Mnemonic := '.';
    while (P < Length(S)) and (IsAlpha(S[P]) or (S[P]= Ord('-')) or IsDigit(S[P])) do
    begin
      Mnemonic := Mnemonic + Chr(S[P]);
      P := P + 1;
    end;
    Result.Mnemonic := Mnemonic;
    { Rest is raw args — stored in RawLine for directive handlers }
    while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
      P := P + 1;
    Result.RawLine := Copy(S, P, Length(S) - P);
    Exit;
  end;

  { Instruction }
  Result.Kind := lkInstr;
  P := 0;
  Mnemonic := '';
  while (P < Length(S)) and (IsAlnum(S[P])) do
  begin
    Mnemonic := Mnemonic + Chr(S[P]);
    P := P + 1;
  end;

  { `lock` prefix: record it and read the real mnemonic that follows. }
  if Mnemonic = 'lock' then
  begin
    Result.HasLock := True;
    while (P < Length(S)) and ((S[P] = Ord(' ')) or (S[P] = 9)) do
      P := P + 1;
    Mnemonic := '';
    while (P < Length(S)) and (IsAlnum(S[P])) do
    begin
      Mnemonic := Mnemonic + Chr(S[P]);
      P := P + 1;
    end;
  end;

  Result.Mnemonic := Mnemonic;

  { Skip whitespace }
  while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
    P := P + 1;

  if P >= Length(S) then Exit;

  { Parse first operand }
  TmpOp := ParseOperand(S, P, OpEnd);
  Result.Op1 := TmpOp;
  if Result.Op1.Kind <> opNone then
    Result.NumOps := 1;
  P := OpEnd;

  { Skip comma and whitespace }
  while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
    P := P + 1;
  if (P < Length(S)) and (S[P]= Ord(',')) then
  begin
    P := P + 1;
    while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
      P := P + 1;
    TmpOp := ParseOperand(S, P, OpEnd);
    Result.Op2 := TmpOp;
    if Result.Op2.Kind <> opNone then
      Result.NumOps := 2;
    P := OpEnd;

    { Third operand (VEX 3-operand forms, e.g. vpaddb %ymm2,%ymm3,%ymm3, and
      imm-prefixed forms like pshufd $0x0E,%xmm3,%xmm3). }
    while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
      P := P + 1;
    if (P < Length(S)) and (S[P]= Ord(',')) then
    begin
      P := P + 1;
      while (P < Length(S)) and ((S[P]= Ord(' ')) or (S[P]= 9)) do
        P := P + 1;
      TmpOp := ParseOperand(S, P, OpEnd);
      Result.Op3 := TmpOp;
      if Result.Op3.Kind <> opNone then
        Result.NumOps := 3;
    end;
  end;
end;

{ ---- x86-64 instruction encoding ------------------------------------- }

{ REX prefix: 0100 WRXB
  W = 1 for 64-bit operand size
  R = extends ModRM.reg
  X = extends SIB.index
  B = extends ModRM.rm or SIB.base }
function MakeRex(AW, AR, AX, AB: Boolean): Integer;
begin
  Result := $40;
  if AW then Result := Result or $08;
  if AR then Result := Result or $04;
  if AX then Result := Result or $02;
  if AB then Result := Result or $01;
end;

function NeedsRex(ACode: Integer): Boolean;
begin
  Result := ACode >= 8;
end;

{ ModRM byte: mod(2) reg(3) rm(3) }
function MakeModRM(AMod, AReg, ARM: Integer): Integer;
begin
  Result := ((AMod and 3) shl 6) or ((AReg and 7) shl 3) or (ARM and 7);
end;

{ SIB byte: scale(2) index(3) base(3) }
function MakeSIB(AScale, AIndex, ABase: Integer): Integer;
var
  SS: Integer;
begin
  case AScale of
    1: SS := 0;
    2: SS := 1;
    4: SS := 2;
    8: SS := 3;
  else
    SS := 0;
  end;
  Result := (SS shl 6) or ((AIndex and 7) shl 3) or (ABase and 7);
end;

type
  TCodeBuf = record
    Data: string;
    Len:  Integer;
  end;

procedure CBInit(var ACB: TCodeBuf);
begin
  ACB.Data := '';
  ACB.Len := 0;
end;

procedure CBEmit(var ACB: TCodeBuf; AByte: Integer);
begin
  ACB.Data := ACB.Data + Chr(AByte and $FF);
  ACB.Len := ACB.Len + 1;
end;

{ Insert a byte at the front of the buffer.  Used for legacy prefixes
  (segment overrides) that must precede REX, which the caller has
  already emitted. }
procedure CBPrepend(var ACB: TCodeBuf; AByte: Integer);
begin
  ACB.Data := Chr(AByte and $FF) + ACB.Data;
  ACB.Len := ACB.Len + 1;
end;

procedure CBPatch32(var ACB: TCodeBuf; AOffset: Integer; AVal: Integer);
var
  P: PChar;
begin
  P := PChar(ACB.Data);
  P[AOffset]     := Chr(AVal and $FF);
  P[AOffset + 1] := Chr((AVal shr 8) and $FF);
  P[AOffset + 2] := Chr((AVal shr 16) and $FF);
  P[AOffset + 3] := Chr((AVal shr 24) and $FF);
end;

procedure CBEmit16(var ACB: TCodeBuf; AVal: Integer);
begin
  CBEmit(ACB, AVal and $FF);
  CBEmit(ACB, (AVal shr 8) and $FF);
end;

procedure CBEmit32(var ACB: TCodeBuf; AVal: Integer);
begin
  CBEmit(ACB, AVal and $FF);
  CBEmit(ACB, (AVal shr 8) and $FF);
  CBEmit(ACB, (AVal shr 16) and $FF);
  CBEmit(ACB, (AVal shr 24) and $FF);
end;

procedure CBEmit64(var ACB: TCodeBuf; AVal: Int64);
begin
  CBEmit32(ACB, Integer(AVal and $FFFFFFFF));
  CBEmit32(ACB, Integer((AVal shr 32) and $FFFFFFFF));
end;

{ Emit ModRM + optional SIB + displacement for a memory operand.
  AReg is the /r field (register code 0-7).
  ABase, AIndex, AScale, ADisp describe the memory address.
  Returns True if a 32-bit displacement was emitted at the end
  (for relocation patching). }
function EmitModRMMem(var ACB: TCodeBuf; AReg: Integer;
  ABase, AIndex, AScale: Integer; ADisp: Int64;
  out ADispOffset: Integer): Boolean;
var
  ModBits: Integer;
  NeedSIB: Boolean;
  BaseEnc: Integer;
begin
  Result := False;
  ADispOffset := 0;
  NeedSIB := (AIndex >= 0) or ((ABase and 7) = 4);

  if ABase < 0 then
  begin
    { No base register — use disp32 addressing (mod=00, rm=100 + SIB,
      or mod=00 rm=101 for RIP-relative which is handled elsewhere) }
    CBEmit(ACB, MakeModRM(0, AReg, 4));
    if AIndex >= 0 then
      CBEmit(ACB, MakeSIB(AScale, AIndex, 5))
    else
      CBEmit(ACB, MakeSIB(1, 4, 5));
    ADispOffset := ACB.Len;
    CBEmit32(ACB, Integer(ADisp));
    Result := True;
    Exit;
  end;

  BaseEnc := ABase and 7;

  if (ADisp = 0) and (BaseEnc <> 5) then
    ModBits := 0
  else if (ADisp >= -128) and (ADisp <= 127) then
    ModBits := 1
  else
    ModBits := 2;

  if NeedSIB then
  begin
    CBEmit(ACB, MakeModRM(ModBits, AReg, 4));
    if AIndex >= 0 then
      CBEmit(ACB, MakeSIB(AScale, AIndex, ABase))
    else
      CBEmit(ACB, MakeSIB(1, 4, ABase));
  end
  else
    CBEmit(ACB, MakeModRM(ModBits, AReg, ABase));

  if ModBits = 1 then
    CBEmit(ACB, Integer(ADisp) and $FF)
  else if ModBits = 2 then
  begin
    ADispOffset := ACB.Len;
    CBEmit32(ACB, Integer(ADisp));
    Result := True;
  end;
end;

{ Emit ModRM for RIP-relative addressing.  The 32-bit displacement
  placeholder is always emitted (filled in by relocation). }
procedure EmitModRMRip(var ACB: TCodeBuf; AReg: Integer;
  out ADispOffset: Integer);
begin
  CBEmit(ACB, MakeModRM(0, AReg, 5));
  ADispOffset := ACB.Len;
  CBEmit32(ACB, 0);
end;

{ ---- Instruction encoder ---------------------------------------------- }

{ The encoder is organised by instruction pattern.  Each mnemonic maps to
  a handler that emits the correct prefix + opcode + ModRM + displacement
  + immediate bytes.

  Naming: the AT&T suffix (b/w/l/q) determines operand size.  In AT&T
  syntax, source is Op1, destination is Op2 (reversed from Intel). }

type
  TRelocRequest = record
    Section:  TContainerSectionKind;
    Offset:   Integer;
    Symbol:   string;
    RType:    TContainerRelocKind;
    Addend:   Int64;
  end;

  TEncodeContext = record
    Section:  TContainerSectionKind;
    Offset:   Integer;
    Relocs:      array of TRelocRequest;
    RelocCount:  Integer;
    Labels:   TLabelMap;
    Pass:     Integer;
    { Number of immediate bytes the current instruction emits AFTER the
      RIP-relative displacement field.  PC-relative fixups are relative
      to the END of the instruction, so both the in-section patch and
      the relocation addend must account for these trailing bytes.
      Set by imm->mem encoders before EncodeMemOperand; reset per
      instruction. }
    ImmTail:  Integer;
  end;

function EncodeInstruction(var ACtx: TEncodeContext;
  const AParsed: TParsedLine): string; forward;

function EncodeMovGeneric(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;

function EncodeALU(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;

function EncodeIMul(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const ASrc, ADst: TOperand): string; forward;

function EncodeXchg(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;

function EncodeShift(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;

function EncodeMovExtend(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;

function EncodeSSE(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;
function EncodeMovqXmm(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string; forward;
{ VEX/AVX encoder.  AOp1/AOp2/AOp3 are the parsed operands in AT&T order
  (AOp1 = first / source-or-immediate ... AOp3 = destination). }
function EncodeVEX(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const AOp1, AOp2, AOp3: TOperand): string; forward;

{ Returns True if the mnemonic is a conditional or unconditional branch }
function IsBranch(const AMnem: string): Boolean;
begin
  Result := (AMnem = 'jmp') or (AMnem = 'je') or (AMnem = 'jne')
         or (AMnem = 'jl') or (AMnem = 'jg') or (AMnem = 'jle')
         or (AMnem = 'jge') or (AMnem = 'ja') or (AMnem = 'jae')
         or (AMnem = 'jb') or (AMnem = 'jbe') or (AMnem = 'jnz')
         or (AMnem = 'jz');
end;

function BranchCondCode(const AMnem: string): Integer;
begin
  if AMnem = 'jo'  then Result := $0
  else if AMnem = 'jno' then Result := $1
  else if (AMnem = 'jb') or (AMnem = 'jnae') then Result := $2
  else if (AMnem = 'jae') or (AMnem = 'jnb') then Result := $3
  else if (AMnem = 'je') or (AMnem = 'jz') then Result := $4
  else if (AMnem = 'jne') or (AMnem = 'jnz') then Result := $5
  else if AMnem = 'jbe' then Result := $6
  else if AMnem = 'ja'  then Result := $7
  else if AMnem = 'jl'  then Result := $C
  else if AMnem = 'jge' then Result := $D
  else if AMnem = 'jle' then Result := $E
  else if AMnem = 'jg'  then Result := $F
  else Result := -1;
end;

function SetCCOpcode(const AMnem: string): Integer;
begin
  if AMnem = 'sete'  then Result := $94
  else if AMnem = 'setne' then Result := $95
  else if AMnem = 'setl'  then Result := $9C
  else if AMnem = 'setge' then Result := $9D
  else if AMnem = 'setle' then Result := $9E
  else if AMnem = 'setg'  then Result := $9F
  else if AMnem = 'seta'  then Result := $97
  else if AMnem = 'setae' then Result := $93
  else if AMnem = 'setb'  then Result := $92
  else if AMnem = 'setbe' then Result := $96
  else Result := -1;
end;

function IsSetCC(const AMnem: string): Boolean;
begin
  Result := SetCCOpcode(AMnem) >= 0;
end;

{ ---- TLabelMap ---------------------------------------------------------- }

constructor TLabelMap.Create;
begin
  inherited Create();
  FIndex := TDictionary<string, Integer>.Create();
  SetLength(FKeys, 0);
  SetLength(FVals, 0);
  FCount := 0;
end;

destructor TLabelMap.Destroy;
begin
  FIndex.Free();
  SetLength(FKeys, 0);
  SetLength(FVals, 0);
  inherited Destroy();
end;

procedure TLabelMap.Add(const AKey: string; AVal: TLabelInfo);
var
  Idx: Integer;
begin
  if FIndex.TryGetValue(AKey, Idx) then
  begin
    FVals[Idx] := AVal;
    Exit;
  end;
  if FCount = Length(FKeys) then
  begin
    SetLength(FKeys, FCount * 2 + 8);
    SetLength(FVals, FCount * 2 + 8);
  end;
  FKeys[FCount] := AKey;
  FVals[FCount] := AVal;
  FIndex.Add(AKey, FCount);
  FCount := FCount + 1;
end;

procedure TLabelMap.Remove(const AKey: string);
begin
  // Not needed — Add overwrites existing entries.
  // Kept for API compatibility; does nothing.
end;

function TLabelMap.ContainsKey(const AKey: string): Boolean;
begin
  Result := FIndex.ContainsKey(AKey);
end;

function TLabelMap.TryGetValue(const AKey: string; var AVal: TLabelInfo): Boolean;
var
  Idx: Integer;
begin
  if FIndex.TryGetValue(AKey, Idx) then
  begin
    AVal := FVals[Idx];
    Result := True;
  end
  else
    Result := False;
end;

function TLabelMap.GetKey(AIdx: Integer): string;
begin
  Result := FKeys[AIdx];
end;

function TLabelMap.GetVal(AIdx: Integer): TLabelInfo;
begin
  Result := FVals[AIdx];
end;

{ Add a relocation request to the context }
procedure AddRelocReq(var ACtx: TEncodeContext; AOffset: Integer;
  const ASym: string; ARType: TContainerRelocKind; AAddend: Int64);
var
  R: TRelocRequest;
begin
  R.Section := ACtx.Section;
  R.Offset  := AOffset;
  R.Symbol  := ASym;
  R.RType   := ARType;
  R.Addend  := AAddend;
  if ACtx.RelocCount = Length(ACtx.Relocs) then
    SetLength(ACtx.Relocs, ACtx.RelocCount * 2 + 8);
  ACtx.Relocs[ACtx.RelocCount] := R;
  ACtx.RelocCount := ACtx.RelocCount + 1;
end;

{ Encode a RIP-relative memory operand, emitting a relocation. }
procedure EncodeRipRelOperand(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AOp: TOperand; AReg: Integer);
var
  DispOff: Integer;
  LabelInf: TLabelInfo;
  PcRelDisp: Integer;
begin
  EmitModRMRip(ACB, AReg, DispOff);
  if (ACtx.Pass = 2) and (AOp.Sym <> '') and
     ACtx.Labels.TryGetValue(AOp.Sym, LabelInf) and
     (LabelInf.Section = ACtx.Section) then
  begin
    PcRelDisp := (LabelInf.Offset + Integer(AOp.SymDisp))
                 - (ACtx.Offset + DispOff + 4 + ACtx.ImmTail);
    CBPatch32(ACB, DispOff, PcRelDisp);
  end
  else
    AddRelocReq(ACtx, ACtx.Offset + DispOff, AOp.Sym, crkPC32,
                AOp.SymDisp - 4 - ACtx.ImmTail);
end;

{ Encode a TLS memory operand (%fs:sym@tpoff or %fs:disp). }
procedure EncodeTLSOperand(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AOp: TOperand; AReg: Integer);
var
  DispOff: Integer;
begin
  CBPrepend(ACB, $64);
  CBEmit(ACB, MakeModRM(0, AReg, 4));
  CBEmit(ACB, MakeSIB(1, 4, 5));
  DispOff := ACB.Len;
  if AOp.Sym <> '' then
  begin
    CBEmit32(ACB, 0);
    AddRelocReq(ACtx, ACtx.Offset + DispOff, AOp.Sym, crkTPOFF32, 0);
  end
  else
    CBEmit32(ACB, Integer(AOp.Disp));
end;

{ Encode a memory or RIP-relative or TLS source/dest operand. }
procedure EncodeMemOperand(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AOp: TOperand; AReg: Integer);
var
  DispOff: Integer;
  Dummy: Boolean;
begin
  case AOp.Kind of
    opRipRel: EncodeRipRelOperand(ACB, ACtx, AOp, AReg);
    opTLS:    EncodeTLSOperand(ACB, ACtx, AOp, AReg);
    opMem:
    begin
      if AOp.TpOff and (AOp.Sym <> '') then
      begin
        Dummy := EmitModRMMem(ACB, AReg, AOp.Base, AOp.Index, AOp.Scale,
                              $7FFFFFFF, DispOff);
        CBPatch32(ACB, DispOff, 0);
        AddRelocReq(ACtx, ACtx.Offset + DispOff, AOp.Sym, crkTPOFF32,
                    AOp.SymDisp);
      end
      else if AOp.Sym <> '' then
      begin
        EncodeRipRelOperand(ACB, ACtx, AOp, AReg);
      end
      else
        Dummy := EmitModRMMem(ACB, AReg, AOp.Base, AOp.Index, AOp.Scale,
                              AOp.Disp, DispOff);
    end;
  else
    { The remaining TOperandKind values (opNone/opReg/opImm/opImm64/opLabel/
      opIndirect) are not MEMORY operands and never reach this encoder — the
      caller dispatches them elsewhere.  Stated explicitly so a new operand
      kind fails loudly here instead of silently encoding nothing. }
    raise EAssembler.Create('EncodeMemOperand: non-memory operand kind '
      + IntToStr(Ord(AOp.Kind)));
  end;
end;

function IsMemLike(const AOp: TOperand): Boolean;
begin
  Result := (AOp.Kind = opMem) or (AOp.Kind = opRipRel) or (AOp.Kind = opTLS);
end;

{ Emit REX prefix if needed for a reg-reg or reg-mem instruction.
  AW = 64-bit operand size, AReg/ARM are register codes (may be >= 8). }
procedure EmitRexIfNeeded(var ACB: TCodeBuf; AW: Boolean;
  AReg, ARM: Integer; AForce8BitRex: Boolean);
var
  NeedRex: Boolean;
begin
  NeedRex := AW or (AReg >= 8) or (ARM >= 8) or AForce8BitRex;
  if NeedRex then
    CBEmit(ACB, MakeRex(AW, AReg >= 8, False, ARM >= 8));
end;

procedure EmitRexWithIndex(var ACB: TCodeBuf; AW: Boolean;
  AReg, AIndex, ABase: Integer);
var
  NeedRex: Boolean;
begin
  NeedRex := AW or (AReg >= 8) or (AIndex >= 8) or (ABase >= 8);
  if NeedRex then
    CBEmit(ACB, MakeRex(AW, AReg >= 8, AIndex >= 8, ABase >= 8));
end;

{ Emit the REX prefix for an instruction with a memory operand, taking
  base AND index extension bits into account.  Every mem-operand path
  must use this (or EmitRexWithIndex) — computing REX from the base
  register alone silently mis-encodes r8-r15 index registers as their
  low-3-bit twins. }
procedure EmitRexForMem(var ACB: TCodeBuf; AW: Boolean; AReg: Integer;
  const AMem: TOperand; AForce8BitRex: Boolean);
var
  BaseReg: Integer;
  NeedRex: Boolean;
begin
  BaseReg := AMem.Base;
  if BaseReg < 0 then BaseReg := 0;
  NeedRex := AW or (AReg >= 8) or (BaseReg >= 8) or (AMem.Index >= 8)
             or AForce8BitRex;
  if NeedRex then
    CBEmit(ACB, MakeRex(AW, AReg >= 8, AMem.Index >= 8, BaseReg >= 8));
end;

{ Is this an 8-bit register that requires REX prefix for uniform encoding?
  (spl, bpl, sil, dil need REX to distinguish from ah/ch/dh/bh) }
function NeedsRex8(ARegCode: Integer; AWidth: Integer): Boolean;
begin
  Result := (AWidth = 8) and (ARegCode >= 4) and (ARegCode <= 7);
end;

{ Map an unsuffixed AT&T mnemonic (mov/lea/xor/…) to its size-suffixed form,
  inferring the operand size from a register operand's width (GNU as does the
  same).  Mnemonics that already carry a suffix, and ones that are size-fixed in
  long mode (push/pop/call/jmp are 64-bit), pass through.  64-bit is the default
  when no register operand pins the width. }
function NormalizeMnemonic(const AMnem: string;
  const AOp1, AOp2: TOperand): string;
var
  W: Integer;
  Suffix: string;
begin
  Result := AMnem;
  { Width from whichever operand is a register (Op2 first — it is the
    destination in AT&T two-operand forms). }
  W := 0;
  if AOp2.Kind = opReg then W := AOp2.RegW
  else if AOp1.Kind = opReg then W := AOp1.RegW;
  if W = 64 then Suffix := 'q'
  else if W = 32 then Suffix := 'l'
  else if W = 16 then Suffix := 'w'
  else if W = 8 then Suffix := 'b'
  else Suffix := 'q';   { default 64-bit when no register pins the size }

  { Size-inferred integer ALU/data mnemonics. }
  if (AMnem = 'mov') or (AMnem = 'xor') or (AMnem = 'and') or (AMnem = 'or') or
     (AMnem = 'add') or (AMnem = 'sub') or (AMnem = 'cmp') or (AMnem = 'test') or
     (AMnem = 'inc') or (AMnem = 'dec') or (AMnem = 'neg') or (AMnem = 'not') or
     (AMnem = 'imul') or (AMnem = 'shl') or (AMnem = 'shr') then
    Result := AMnem + Suffix
  { lea's size is the destination pointer width — always 64-bit here. }
  else if AMnem = 'lea' then
    Result := 'leaq'
  { Stack/branch ops are 64-bit-only in long mode. }
  else if AMnem = 'push' then Result := 'pushq'
  else if AMnem = 'pop'  then Result := 'popq'
  else if AMnem = 'call' then Result := 'callq';
  { 'jmp' keeps its name (the encoder already handles jmp incl. indirect). }
end;

{ ---- Main instruction encoder ----------------------------------------- }

function EncodeInstruction(var ACtx: TEncodeContext;
  const AParsed: TParsedLine): string;
var
  CB: TCodeBuf;
  Mnem: string;
  Op1, Op2, Op3: TOperand;
  DispOff: Integer;
  Dummy: Boolean;
  TargetOff: Integer;
  RelDisp: Int64;
  CC: Integer;
  Info: TLabelInfo;
begin
  CBInit(CB);
  ACtx.ImmTail := 0;
  Op1 := AParsed.Op1;
  Op2 := AParsed.Op2;
  Op3 := AParsed.Op3;
  { Accept unsuffixed AT&T mnemonics (mov/lea/xor/…) by inferring the size. }
  Mnem := NormalizeMnemonic(AParsed.Mnemonic, Op1, Op2);

  { ---- lock prefix (F0) — emitted ahead of the instruction it guards ---- }
  if AParsed.HasLock then
    CBEmit(CB, $F0);

  { ---- ret ---- }
  if Mnem = 'ret' then
  begin
    CBEmit(CB, $C3);
    Result := CB.Data;
    Exit;
  end;

  { ---- endbr64 (CET) ---- F3 0F 1E FA }
  if Mnem = 'endbr64' then
  begin
    CBEmit(CB, $F3); CBEmit(CB, $0F); CBEmit(CB, $1E); CBEmit(CB, $FA);
    Result := CB.Data;
    Exit;
  end;

  { ---- hlt ---- F4 }
  if Mnem = 'hlt' then
  begin
    CBEmit(CB, $F4);
    Result := CB.Data;
    Exit;
  end;

  { ---- syscall ---- 0F 05 }
  if Mnem = 'syscall' then
  begin
    CBEmit(CB, $0F); CBEmit(CB, $05);
    Result := CB.Data;
    Exit;
  end;

  { ---- cpuid ---- 0F A2 }
  if Mnem = 'cpuid' then
  begin
    CBEmit(CB, $0F); CBEmit(CB, $A2);
    Result := CB.Data;
    Exit;
  end;

  { ---- leave ---- }
  if Mnem = 'leave' then
  begin
    CBEmit(CB, $C9);
    Result := CB.Data;
    Exit;
  end;

  { ---- cltd (cdq) ---- }
  if Mnem = 'cltd' then
  begin
    CBEmit(CB, $99);
    Result := CB.Data;
    Exit;
  end;

  { ---- cqto (cqo) ---- }
  if Mnem = 'cqto' then
  begin
    CBEmit(CB, MakeRex(True, False, False, False));
    CBEmit(CB, $99);
    Result := CB.Data;
    Exit;
  end;

  { ---- nop ---- }
  if Mnem = 'nop' then
  begin
    CBEmit(CB, $90);
    Result := CB.Data;
    Exit;
  end;

  { ---- pushq ---- }
  if Mnem = 'pushq' then
  begin
    if Op1.Kind = opReg then
    begin
      if Op1.Reg >= 8 then
        CBEmit(CB, MakeRex(False, False, False, True));
      CBEmit(CB, $50 + (Op1.Reg and 7));
    end
    else if Op1.Kind = opImm then
    begin
      if (Op1.Imm >= -128) and (Op1.Imm <= 127) then
      begin
        CBEmit(CB, $6A);
        CBEmit(CB, Integer(Op1.Imm) and $FF);
      end
      else
      begin
        CBEmit(CB, $68);
        CBEmit32(CB, Integer(Op1.Imm));
      end;
    end
    else if IsMemLike(Op1) then
    begin
      EmitRexForMem(CB, False, 0, Op1, False);
      CBEmit(CB, $FF);
      EncodeMemOperand(CB, ACtx, Op1, 6);
    end
    else
      raise EAssembler.Create('pushq: unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- popq ---- }
  if Mnem = 'popq' then
  begin
    if Op1.Kind = opReg then
    begin
      if Op1.Reg >= 8 then
        CBEmit(CB, MakeRex(False, False, False, True));
      CBEmit(CB, $58 + (Op1.Reg and 7));
    end
    else
      raise EAssembler.Create('popq: unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- callq ---- }
  if Mnem = 'callq' then
  begin
    if Op1.Kind = opIndirect then
    begin
      if Op1.Reg >= 8 then
        CBEmit(CB, MakeRex(False, False, False, True));
      CBEmit(CB, $FF);
      CBEmit(CB, MakeModRM(3, 2, Op1.Reg));
    end
    else if Op1.Kind = opLabel then
    begin
      CBEmit(CB, $E8);
      DispOff := CB.Len;
      CBEmit32(CB, 0);
      if ACtx.Labels.TryGetValue(Op1.Sym, Info) then
      begin
        if Info.Defined and (Info.Section = ACtx.Section) then
        begin
          RelDisp := Int64(Info.Offset) - Int64(ACtx.Offset + CB.Len);
          CBPatch32(CB, DispOff, Integer(RelDisp));
        end
        else
          AddRelocReq(ACtx, ACtx.Offset + DispOff, Op1.Sym, crkPLT32, -4);
      end
      else
        AddRelocReq(ACtx, ACtx.Offset + DispOff, Op1.Sym, crkPLT32, -4);
    end
    else if IsMemLike(Op1) then
    begin
      EmitRexForMem(CB, False, 0, Op1, False);
      CBEmit(CB, $FF);
      EncodeMemOperand(CB, ACtx, Op1, 2);
    end
    else
      raise EAssembler.Create('callq: unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- branches (jmp, jcc) ---- }
  if IsBranch(Mnem) then
  begin
    if (Op1.Kind = opLabel) then
    begin
      if Mnem = 'jmp' then
      begin
        CBEmit(CB, $E9);
        DispOff := CB.Len;
        CBEmit32(CB, 0);
      end
      else
      begin
        CC := BranchCondCode(Mnem);
        CBEmit(CB, $0F);
        CBEmit(CB, $80 + CC);
        DispOff := CB.Len;
        CBEmit32(CB, 0);
      end;
      if ACtx.Labels.TryGetValue(Op1.Sym, Info) and Info.Defined
         and (Info.Section = ACtx.Section) then
      begin
        RelDisp := Int64(Info.Offset) - Int64(ACtx.Offset + CB.Len);
        CBPatch32(CB, DispOff, Integer(RelDisp));
      end
      else
        { External or other-section target: emit a relocation rather
          than silently encoding displacement 0 (a jump to the next
          instruction). }
        AddRelocReq(ACtx, ACtx.Offset + DispOff, Op1.Sym, crkPLT32,
                    Int64(-4));
    end
    else if (Op1.Kind = opIndirect) then
    begin
      { Register-indirect: jmp *%reg / call *%reg.  FF /4 (jmp) or /2 (call). }
      if Op1.Reg >= 8 then
        CBEmit(CB, MakeRex(False, False, False, True));
      CBEmit(CB, $FF);
      if Mnem = 'jmp' then
        CBEmit(CB, MakeModRM(3, 4, Op1.Reg))
      else
        CBEmit(CB, MakeModRM(3, 2, Op1.Reg));
    end
    else if IsMemLike(Op1) and Op1.Indirect then
    begin
      { Memory-indirect: jmp *disp(%reg) / call *disp(%reg).  FF /4 or /2 with
        the memory ModRM. }
      EmitRexForMem(CB, False, 0, Op1, False);
      CBEmit(CB, $FF);
      if Mnem = 'jmp' then
        EncodeMemOperand(CB, ACtx, Op1, 4)
      else
        EncodeMemOperand(CB, ACtx, Op1, 2);
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- setcc ---- }
  if IsSetCC(Mnem) then
  begin
    if Op1.Kind = opReg then
    begin
      if (Op1.Reg >= 8) or NeedsRex8(Op1.Reg, Op1.RegW) then
        CBEmit(CB, MakeRex(False, False, False, Op1.Reg >= 8));
      CBEmit(CB, $0F);
      CBEmit(CB, SetCCOpcode(Mnem));
      CBEmit(CB, MakeModRM(3, 0, Op1.Reg));
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- movabsq $imm64, %reg ---- }
  if Mnem = 'movabsq' then
  begin
    if (Op1.Kind = opImm) and (Op2.Kind = opReg) then
    begin
      CBEmit(CB, MakeRex(True, False, False, Op2.Reg >= 8));
      CBEmit(CB, $B8 + (Op2.Reg and 7));
      CBEmit64(CB, Op1.Imm);
    end
    else
      raise EAssembler.Create('movabsq: expected $imm64, %reg');
    Result := CB.Data;
    Exit;
  end;

  { ---- movq/movd between an XMM register and a GP register/memory ----
    `movq %xmm, %r64` and `movq %r64, %xmm` are SSE moves (66 [REX.W] 0F 7E/6E),
    NOT the integer reg-reg mov.  Without this an `movq %xmm0, %rax` was encoded
    as `mov %rax,%rax` (both operands read as GP reg 0), silently dropping the
    xmm value — the cause of float args reaching Format() as garbage. }
  if ((Mnem = 'movq') or (Mnem = 'movd')) and (Op1.IsXmm or Op2.IsXmm) then
  begin
    Result := EncodeMovqXmm(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- movq/movl/movw/movb ---- }
  if (Mnem = 'movq') or (Mnem = 'movl') or (Mnem = 'movw')
     or (Mnem = 'movb') then
  begin
    Result := EncodeMovGeneric(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- leaq ---- }
  if Mnem = 'leaq' then
  begin
    if IsMemLike(Op1) and (Op2.Kind = opReg) then
    begin
      EmitRexForMem(CB, True, Op2.Reg, Op1, False);
      CBEmit(CB, $8D);
      EncodeMemOperand(CB, ACtx, Op1, Op2.Reg and 7);
    end
    else
      raise EAssembler.Create('leaq: unsupported operands');
    Result := CB.Data;
    Exit;
  end;

  { ---- addq/addl/subq/subl/andq/andl/orq/orl/xorq/xorl/cmpq/cmpl/testq/testl ---- }
  if (Mnem = 'addq') or (Mnem = 'addl') or (Mnem = 'subq') or (Mnem = 'subl')
     or (Mnem = 'andq') or (Mnem = 'andl') or (Mnem = 'orq') or (Mnem = 'orl')
     or (Mnem = 'xorq') or (Mnem = 'xorl') or (Mnem = 'cmpq') or (Mnem = 'cmpl')
     or (Mnem = 'testq') or (Mnem = 'testl') then
  begin
    Result := EncodeALU(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- xchg / cmpxchg (atomic primitives) ----
    AT&T order is `reg, r/m`.  xchg has an implicit lock when r/m is memory;
    cmpxchg compares r/m against %eax/%rax and conditionally swaps in reg.
    Both take the `reg, mem` and `reg, reg` forms the futex mutex needs. }
  if (Mnem = 'xchgl') or (Mnem = 'xchgq')
     or (Mnem = 'cmpxchgl') or (Mnem = 'cmpxchgq') then
  begin
    Result := EncodeXchg(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- imulq ---- }
  if Mnem = 'imulq' then
  begin
    Result := EncodeIMul(CB, ACtx, Op1, Op2);
    Exit;
  end;

  { ---- idivq / divq ---- }
  if (Mnem = 'idivq') or (Mnem = 'divq') then
  begin
    if Op1.Kind = opReg then
    begin
      EmitRexIfNeeded(CB, True, 0, Op1.Reg, False);
      CBEmit(CB, $F7);
      if Mnem = 'idivq' then
        CBEmit(CB, MakeModRM(3, 7, Op1.Reg))
      else
        CBEmit(CB, MakeModRM(3, 6, Op1.Reg));
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- incq / decq ---- }
  if (Mnem = 'incq') or (Mnem = 'decq') or
     (Mnem = 'incl') or (Mnem = 'decl') then
  begin
    { FF /0 = inc, /1 = dec; REX.W only for the 'q' (64-bit) forms. }
    if Op1.Kind = opReg then
    begin
      EmitRexIfNeeded(CB, (Mnem = 'incq') or (Mnem = 'decq'), 0, Op1.Reg, False);
      CBEmit(CB, $FF);
      if (Mnem = 'incq') or (Mnem = 'incl') then
        CBEmit(CB, MakeModRM(3, 0, Op1.Reg))
      else
        CBEmit(CB, MakeModRM(3, 1, Op1.Reg));
    end
    else if IsMemLike(Op1) then
    begin
      EmitRexForMem(CB, (Mnem = 'incq') or (Mnem = 'decq'), 0, Op1, False);
      CBEmit(CB, $FF);
      if (Mnem = 'incq') or (Mnem = 'incl') then
        EncodeMemOperand(CB, ACtx, Op1, 0)
      else
        EncodeMemOperand(CB, ACtx, Op1, 1);
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- notl / notq ---- }
  if (Mnem = 'notl') or (Mnem = 'notq') then
  begin
    if Op1.Kind = opReg then
    begin
      EmitRexIfNeeded(CB, Mnem = 'notq', 0, Op1.Reg, False);
      CBEmit(CB, $F7);
      CBEmit(CB, MakeModRM(3, 2, Op1.Reg));
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- negl / negq ---- (F7 /3, same group as notl/notq) }
  if (Mnem = 'negl') or (Mnem = 'negq') then
  begin
    if Op1.Kind = opReg then
    begin
      EmitRexIfNeeded(CB, Mnem = 'negq', 0, Op1.Reg, False);
      CBEmit(CB, $F7);
      CBEmit(CB, MakeModRM(3, 3, Op1.Reg));
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand');
    Result := CB.Data;
    Exit;
  end;

  { ---- xaddl / xaddq ---- (0F C1 /r: xadd src-reg, r/m).  Atomic with the
    lock prefix (emitted above).  src register is in the ModRM reg field. }
  if (Mnem = 'xaddl') or (Mnem = 'xaddq') then
  begin
    if (Op1.Kind = opReg) and IsMemLike(Op2) then
    begin
      EmitRexForMem(CB, Mnem = 'xaddq', Op1.Reg, Op2, False);
      CBEmit(CB, $0F);
      CBEmit(CB, $C1);
      EncodeMemOperand(CB, ACtx, Op2, Op1.Reg and 7);
    end
    else if (Op1.Kind = opReg) and (Op2.Kind = opReg) then
    begin
      EmitRexIfNeeded(CB, Mnem = 'xaddq', Op1.Reg, Op2.Reg, False);
      CBEmit(CB, $0F);
      CBEmit(CB, $C1);
      CBEmit(CB, MakeModRM(3, Op1.Reg, Op2.Reg));
    end
    else
      raise EAssembler.Create(Mnem + ': unsupported operand combination');
    Result := CB.Data;
    Exit;
  end;

  { ---- shll/shlq/shrl/shrq/sarl/sarq ---- }
  if (Mnem = 'shll') or (Mnem = 'shlq') or (Mnem = 'shrl') or (Mnem = 'shrq')
     or (Mnem = 'sarl') or (Mnem = 'sarq') then
  begin
    Result := EncodeShift(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- movslq / movsbq / movswq / movzbl / movzbq / movzwl / movzwq ---- }
  if (Mnem = 'movslq') or (Mnem = 'movsbq') or (Mnem = 'movswq')
     or (Mnem = 'movzbl') or (Mnem = 'movzbq') or (Mnem = 'movzwl')
     or (Mnem = 'movzwq') then
  begin
    Result := EncodeMovExtend(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- SSE/FP instructions ---- }
  if (Mnem = 'movsd') or (Mnem = 'movss') or (Mnem = 'movapd') or (Mnem = 'movaps')
     or (Mnem = 'addsd') or (Mnem = 'subsd') or (Mnem = 'mulsd') or (Mnem = 'divsd')
     or (Mnem = 'addss') or (Mnem = 'subss') or (Mnem = 'mulss') or (Mnem = 'divss')
     or (Mnem = 'sqrtsd') or (Mnem = 'sqrtss')
     or (Mnem = 'ucomisd') or (Mnem = 'ucomiss')
     or (Mnem = 'xorpd') or (Mnem = 'xorps')
     or (Mnem = 'cvtsd2ss') or (Mnem = 'cvtss2sd')
     or (Mnem = 'cvtsi2sdq') or (Mnem = 'cvtsi2ssq')
     or (Mnem = 'cvtsd2si') or (Mnem = 'cvtss2si')
     or (Mnem = 'cvttsd2si') or (Mnem = 'cvttss2si')
     or (Mnem = 'pxor') or (Mnem = 'movdqa') or (Mnem = 'movdqu')
     or (Mnem = 'paddb') or (Mnem = 'pcmpgtb') or (Mnem = 'pcmpeqb')
     or (Mnem = 'psadbw') or (Mnem = 'pabsb') then
  begin
    Result := EncodeSSE(CB, ACtx, Mnem, Op1, Op2);
    Exit;
  end;

  { ---- pshufd $imm8, xmm/m, xmm  (66 0F 70 /r ib) ---- }
  if Mnem = 'pshufd' then
  begin
    if (Op1.Kind = opImm) and (Op2.Kind = opReg) and (Op3.Kind = opReg) then
    begin
      EmitSSERegReg(CB, $66, False, $70, -1, Op2.Reg, Op3.Reg);
      CBEmit(CB, Integer(Op1.Imm) and $FF);
    end
    else
      raise EAssembler.Create('pshufd: unsupported operands');
    Result := CB.Data;
    Exit;
  end;

  { ---- AVX/AVX2 (VEX-encoded) ---- }
  if (Mnem = 'vzeroupper')
     or (Mnem = 'vpxor') or (Mnem = 'vpaddb') or (Mnem = 'vpaddw')
     or (Mnem = 'vpaddq') or (Mnem = 'vpcmpeqb') or (Mnem = 'vpcmpgtb')
     or (Mnem = 'vpsadbw') or (Mnem = 'vpabsb')
     or (Mnem = 'vmovdqa') or (Mnem = 'vmovdqu') or (Mnem = 'vmovd')
     or (Mnem = 'vpsllw') or (Mnem = 'vpsrlw') or (Mnem = 'vpshufd')
     or (Mnem = 'vextracti128') then
  begin
    Result := EncodeVEX(CB, ACtx, Mnem, Op1, Op2, Op3);
    Exit;
  end;

  raise EAssembler.Create('unhandled mnemonic: ' + Mnem);
end;

{ ---- MOV generic encoder (movq/movl/movw/movb) ----------------------- }

function EncodeMovGeneric(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  W64: Boolean;
  OpSize: Integer;
  Force8Rex: Boolean;
begin
  W64 := (AMnem = 'movq');
  if AMnem = 'movb' then OpSize := 8
  else if AMnem = 'movw' then OpSize := 16
  else if AMnem = 'movl' then OpSize := 32
  else OpSize := 64;

  { reg -> reg }
  if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
  begin
    if OpSize = 16 then CBEmit(ACB, $66);
    Force8Rex := (OpSize = 8) and (NeedsRex8(ASrc.Reg, 8) or NeedsRex8(ADst.Reg, 8));
    EmitRexIfNeeded(ACB, W64, ASrc.Reg, ADst.Reg, Force8Rex);
    if OpSize = 8 then
      CBEmit(ACB, $88)
    else
      CBEmit(ACB, $89);
    CBEmit(ACB, MakeModRM(3, ASrc.Reg, ADst.Reg));
    Result := ACB.Data;
    Exit;
  end;

  { imm -> reg }
  if (ASrc.Kind = opImm) and (ADst.Kind = opReg) then
  begin
    if OpSize = 16 then CBEmit(ACB, $66);
    Force8Rex := (OpSize = 8) and NeedsRex8(ADst.Reg, 8);
    EmitRexIfNeeded(ACB, W64, 0, ADst.Reg, Force8Rex);
    if OpSize = 8 then
    begin
      CBEmit(ACB, $C6);
      CBEmit(ACB, MakeModRM(3, 0, ADst.Reg));
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end
    else if OpSize = 16 then
    begin
      CBEmit(ACB, $C7);
      CBEmit(ACB, MakeModRM(3, 0, ADst.Reg));
      CBEmit16(ACB, Integer(ASrc.Imm));
    end
    else
    begin
      CBEmit(ACB, $C7);
      CBEmit(ACB, MakeModRM(3, 0, ADst.Reg));
      CBEmit32(ACB, Integer(ASrc.Imm));
    end;
    Result := ACB.Data;
    Exit;
  end;

  { reg -> mem/rip/tls }
  if (ASrc.Kind = opReg) and IsMemLike(ADst) then
  begin
    if OpSize = 16 then CBEmit(ACB, $66);
    Force8Rex := (OpSize = 8) and NeedsRex8(ASrc.Reg, 8);
    EmitRexForMem(ACB, W64, ASrc.Reg, ADst, Force8Rex);
    if OpSize = 8 then
      CBEmit(ACB, $88)
    else
      CBEmit(ACB, $89);
    EncodeMemOperand(ACB, ACtx, ADst, ASrc.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  { mem/rip/tls -> reg }
  if IsMemLike(ASrc) and (ADst.Kind = opReg) then
  begin
    if OpSize = 16 then CBEmit(ACB, $66);
    Force8Rex := (OpSize = 8) and NeedsRex8(ADst.Reg, 8);
    EmitRexForMem(ACB, W64, ADst.Reg, ASrc, Force8Rex);
    if OpSize = 8 then
      CBEmit(ACB, $8A)
    else
      CBEmit(ACB, $8B);
    EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  { imm -> mem/rip/tls }
  if (ASrc.Kind = opImm) and IsMemLike(ADst) then
  begin
    if OpSize = 16 then CBEmit(ACB, $66);
    EmitRexForMem(ACB, W64, 0, ADst, False);
    if OpSize = 8 then
    begin
      CBEmit(ACB, $C6);
      ACtx.ImmTail := 1;
      EncodeMemOperand(ACB, ACtx, ADst, 0);
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end
    else if OpSize = 16 then
    begin
      CBEmit(ACB, $C7);
      ACtx.ImmTail := 2;
      EncodeMemOperand(ACB, ACtx, ADst, 0);
      CBEmit16(ACB, Integer(ASrc.Imm));
    end
    else
    begin
      CBEmit(ACB, $C7);
      ACtx.ImmTail := 4;
      EncodeMemOperand(ACB, ACtx, ADst, 0);
      CBEmit32(ACB, Integer(ASrc.Imm));
    end;
    ACtx.ImmTail := 0;
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': unsupported operand combination');
end;

{ ---- ALU encoder (add/sub/and/or/xor/cmp/test) ----------------------- }

function ALUGroup(const AMnem: string): Integer;
begin
  if (AMnem = 'addq') or (AMnem = 'addl') then Result := 0
  else if (AMnem = 'orq') or (AMnem = 'orl') then Result := 1
  else if (AMnem = 'andq') or (AMnem = 'andl') then Result := 4
  else if (AMnem = 'subq') or (AMnem = 'subl') then Result := 5
  else if (AMnem = 'xorq') or (AMnem = 'xorl') then Result := 6
  else if (AMnem = 'cmpq') or (AMnem = 'cmpl') then Result := 7
  else if (AMnem = 'testq') or (AMnem = 'testl') then Result := 8
  else Result := -1;
end;

function EncodeALU(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  Grp: Integer;
  W64: Boolean;
  IsTest: Boolean;
begin
  Grp := ALUGroup(AMnem);
  W64 := (AMnem[Length(AMnem) - 1]= Ord('q')) or (AMnem = 'orq');
  IsTest := Grp = 8;

  { imm, reg }
  if (ASrc.Kind = opImm) and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, W64, 0, ADst.Reg, False);
    if IsTest then
    begin
      if ADst.Reg = 0 then
      begin
        CBEmit(ACB, $A9);
        CBEmit32(ACB, Integer(ASrc.Imm));
      end
      else
      begin
        CBEmit(ACB, $F7);
        CBEmit(ACB, MakeModRM(3, 0, ADst.Reg));
        CBEmit32(ACB, Integer(ASrc.Imm));
      end;
    end
    else if (ASrc.Imm >= -128) and (ASrc.Imm <= 127) then
    begin
      CBEmit(ACB, $83);
      CBEmit(ACB, MakeModRM(3, Grp, ADst.Reg));
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end
    else
    begin
      if ADst.Reg = 0 then
      begin
        CBEmit(ACB, Grp * 8 + 5);
        CBEmit32(ACB, Integer(ASrc.Imm));
      end
      else
      begin
        CBEmit(ACB, $81);
        CBEmit(ACB, MakeModRM(3, Grp, ADst.Reg));
        CBEmit32(ACB, Integer(ASrc.Imm));
      end;
    end;
    Result := ACB.Data;
    Exit;
  end;

  { reg, reg }
  if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, W64, ASrc.Reg, ADst.Reg, False);
    if IsTest then
      CBEmit(ACB, $85)
    else
      CBEmit(ACB, Grp * 8 + 1);
    CBEmit(ACB, MakeModRM(3, ASrc.Reg, ADst.Reg));
    Result := ACB.Data;
    Exit;
  end;

  { reg, mem/rip }
  if (ASrc.Kind = opReg) and IsMemLike(ADst) then
  begin
    EmitRexForMem(ACB, W64, ASrc.Reg, ADst, False);
    if IsTest then
      CBEmit(ACB, $85)
    else
      CBEmit(ACB, Grp * 8 + 1);
    EncodeMemOperand(ACB, ACtx, ADst, ASrc.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  { mem/rip, reg }
  if IsMemLike(ASrc) and (ADst.Kind = opReg) then
  begin
    EmitRexForMem(ACB, W64, ADst.Reg, ASrc, False);
    if IsTest then
      CBEmit(ACB, $85)
    else
      CBEmit(ACB, Grp * 8 + 3);
    EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  { imm, mem/rip }
  if (ASrc.Kind = opImm) and IsMemLike(ADst) then
  begin
    EmitRexForMem(ACB, W64, 0, ADst, False);
    if IsTest then
    begin
      CBEmit(ACB, $F7);
      ACtx.ImmTail := 4;
      EncodeMemOperand(ACB, ACtx, ADst, 0);
      CBEmit32(ACB, Integer(ASrc.Imm));
    end
    else if (ASrc.Imm >= -128) and (ASrc.Imm <= 127) then
    begin
      CBEmit(ACB, $83);
      ACtx.ImmTail := 1;
      EncodeMemOperand(ACB, ACtx, ADst, Grp);
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end
    else
    begin
      CBEmit(ACB, $81);
      ACtx.ImmTail := 4;
      EncodeMemOperand(ACB, ACtx, ADst, Grp);
      CBEmit32(ACB, Integer(ASrc.Imm));
    end;
    ACtx.ImmTail := 0;
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': unsupported operand combination');
end;

{ ---- XCHG / CMPXCHG encoder ------------------------------------------- }

{ Atomic exchange and compare-exchange.  AT&T operand order is `reg, r/m`
  (ASrc = the register, ADst = the register or memory target):
    xchg    %reg, r/m   -> 87 /r  (mem form is implicitly atomic)
    cmpxchg %reg, r/m   -> 0F B1 /r
  Only the forms the futex mutex needs (reg->reg, reg->mem) are encoded. }
function EncodeXchg(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  W64, IsCmpxchg: Boolean;
begin
  { Blaise strings are 0-based: the last character is at Length-1.  Reading
    AMnem[Length(AMnem)] inspected the byte past the end, so W64 was always
    False and the q-suffixed forms lost REX.W (32-bit narrowing). }
  W64 := AMnem[Length(AMnem) - 1] = Ord('q');
  IsCmpxchg := (AMnem = 'cmpxchgl') or (AMnem = 'cmpxchgq');

  if ASrc.Kind <> opReg then
    raise EAssembler.Create(AMnem + ': source must be a register');

  { reg, reg }
  if ADst.Kind = opReg then
  begin
    EmitRexIfNeeded(ACB, W64, ASrc.Reg, ADst.Reg, False);
    if IsCmpxchg then
    begin
      CBEmit(ACB, $0F);
      CBEmit(ACB, $B1);
    end
    else
      CBEmit(ACB, $87);
    CBEmit(ACB, MakeModRM(3, ASrc.Reg, ADst.Reg));
    Result := ACB.Data;
    Exit;
  end;

  { reg, mem/rip }
  if IsMemLike(ADst) then
  begin
    EmitRexForMem(ACB, W64, ASrc.Reg, ADst, False);
    if IsCmpxchg then
    begin
      CBEmit(ACB, $0F);
      CBEmit(ACB, $B1);
    end
    else
      CBEmit(ACB, $87);
    EncodeMemOperand(ACB, ACtx, ADst, ASrc.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': unsupported operand combination');
end;

{ ---- IMUL encoder ----------------------------------------------------- }

function EncodeIMul(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const ASrc, ADst: TOperand): string;
begin
  { imulq %reg (one-operand: RDX:RAX = RAX * reg) }
  if (ADst.Kind = opNone) and (ASrc.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, True, 0, ASrc.Reg, False);
    CBEmit(ACB, $F7);
    CBEmit(ACB, MakeModRM(3, 5, ASrc.Reg));
    Result := ACB.Data;
    Exit;
  end;

  { imulq %src, %dst (two-operand) }
  if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, False);
    CBEmit(ACB, $0F);
    CBEmit(ACB, $AF);
    CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    Result := ACB.Data;
    Exit;
  end;

  { imulq $imm, %src, %dst (three-operand encoded as $imm, %reg) }
  if (ASrc.Kind = opImm) and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, True, ADst.Reg, ADst.Reg, False);
    if (ASrc.Imm >= -128) and (ASrc.Imm <= 127) then
    begin
      CBEmit(ACB, $6B);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ADst.Reg));
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end
    else
    begin
      CBEmit(ACB, $69);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ADst.Reg));
      CBEmit32(ACB, Integer(ASrc.Imm));
    end;
    Result := ACB.Data;
    Exit;
  end;

  { imulq mem, %dst }
  if IsMemLike(ASrc) and (ADst.Kind = opReg) then
  begin
    EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
    CBEmit(ACB, $0F);
    CBEmit(ACB, $AF);
    EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create('imulq: unsupported operand combination');
end;

{ ---- Shift encoder ---------------------------------------------------- }

function EncodeShift(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  W64: Boolean;
  ShiftOp: Integer;
begin
  W64 := (AMnem = 'shlq') or (AMnem = 'shrq') or (AMnem = 'sarq');
  { ModRM /digit selects the shift: /4 = shl, /5 = shr (logical, zero-fill),
    /7 = sar (arithmetic, sign-preserving).  sar is NOT interchangeable with
    shr — it replicates the sign bit, which is what an Int64 `sar` needs to
    keep a negative value negative. }
  if (AMnem = 'shll') or (AMnem = 'shlq') then ShiftOp := 4
  else if (AMnem = 'sarl') or (AMnem = 'sarq') then ShiftOp := 7
  else ShiftOp := 5;

  { $imm, %reg }
  if (ASrc.Kind = opImm) and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, W64, 0, ADst.Reg, False);
    if ASrc.Imm = 1 then
    begin
      CBEmit(ACB, $D1);
      CBEmit(ACB, MakeModRM(3, ShiftOp, ADst.Reg));
    end
    else
    begin
      CBEmit(ACB, $C1);
      CBEmit(ACB, MakeModRM(3, ShiftOp, ADst.Reg));
      CBEmit(ACB, Integer(ASrc.Imm) and $FF);
    end;
    Result := ACB.Data;
    Exit;
  end;

  { %cl, %reg }
  if (ASrc.Kind = opReg) and (ASrc.Reg = 1) and (ASrc.RegW = 8)
     and (ADst.Kind = opReg) then
  begin
    EmitRexIfNeeded(ACB, W64, 0, ADst.Reg, False);
    CBEmit(ACB, $D3);
    CBEmit(ACB, MakeModRM(3, ShiftOp, ADst.Reg));
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': unsupported operand combination');
end;

{ ---- Move-with-extend encoder ----------------------------------------- }

function EncodeMovExtend(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
begin
  { movslq: sign-extend 32 -> 64 (opcode 63 /r with REX.W) }
  if AMnem = 'movslq' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, False);
      CBEmit(ACB, $63);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
      CBEmit(ACB, $63);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movslq: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movsbq: sign-extend 8 -> 64 (0F BE /r with REX.W) }
  if AMnem = 'movsbq' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $BE);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $BE);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movsbq: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movswq: sign-extend 16 -> 64 (0F BF /r with REX.W) }
  if AMnem = 'movswq' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $BF);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $BF);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movswq: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movzbl: zero-extend 8 -> 32 (0F B6 /r, no REX.W) }
  if AMnem = 'movzbl' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      if (ASrc.Reg >= 8) or (ADst.Reg >= 8) or NeedsRex8(ASrc.Reg, 8) then
        CBEmit(ACB, MakeRex(False, ADst.Reg >= 8, False, ASrc.Reg >= 8));
      CBEmit(ACB, $0F); CBEmit(ACB, $B6);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, False, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B6);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movzbl: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movzbq: zero-extend 8 -> 64 (0F B6 /r with REX.W) }
  if AMnem = 'movzbq' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, NeedsRex8(ASrc.Reg, 8));
      CBEmit(ACB, $0F); CBEmit(ACB, $B6);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B6);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movzbq: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movzwl: zero-extend 16 -> 32 (0F B7 /r, no REX.W) }
  if AMnem = 'movzwl' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, False, ADst.Reg, ASrc.Reg, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B7);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, False, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B7);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movzwl: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  { movzwq: zero-extend 16 -> 64 (0F B7 /r with REX.W) }
  if AMnem = 'movzwq' then
  begin
    if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
    begin
      EmitRexIfNeeded(ACB, True, ADst.Reg, ASrc.Reg, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B7);
      CBEmit(ACB, MakeModRM(3, ADst.Reg, ASrc.Reg));
    end
    else if IsMemLike(ASrc) and (ADst.Kind = opReg) then
    begin
      EmitRexForMem(ACB, True, ADst.Reg, ASrc, False);
      CBEmit(ACB, $0F); CBEmit(ACB, $B7);
      EncodeMemOperand(ACB, ACtx, ASrc, ADst.Reg and 7);
    end
    else
      raise EAssembler.Create('movzwq: unsupported operands');
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': not implemented');
end;

{ ---- VEX (AVX/AVX2) helpers ----------------------------------------- }

{ pp (mandatory-prefix) field: 0=none, 1=66, 2=F3, 3=F2. }
function VexPP(APrefix: Integer): Integer;
begin
  case APrefix of
    $66: Result := 1;
    $F3: Result := 2;
    $F2: Result := 3;
  else
    Result := 0;
  end;
end;

{ Emit a VEX-encoded instruction.  AMap is the opcode map (1 = 0F, 2 = 0F38,
  3 = 0F3A).  ADstReg goes in ModRM.reg, ARmReg/ARmMem in ModRM.r/m, AVvvv is
  the non-destructive source register (the VEX.vvvv field; pass 15 / unused for
  two-operand forms).  AL256 selects the 256-bit (ymm) form (VEX.L).  AW is
  VEX.W.  The 2-byte form (C5) is used when X=B=0, map=1 and W=0; otherwise the
  3-byte form (C4) is required. }
procedure EmitVexRR(var ACB: TCodeBuf; APrefix, AMap: Integer;
  AW, AL256: Boolean; AOpcode, ADstReg, AVvvv, ARmReg: Integer);
var
  R, X, B, PP, Byte2, Byte3: Integer;
begin
  R := Ord(ADstReg >= 8);   { ModRM.reg extension }
  X := 0;
  B := Ord(ARmReg >= 8);    { ModRM.r/m extension }
  PP := VexPP(APrefix);

  if (AMap = 1) and (not AW) and (X = 0) and (B = 0) then
  begin
    { 2-byte VEX (C5).  Byte2 = ~R<<7 | ~vvvv<<3 | L<<2 | pp }
    Byte2 := ((1 - R) shl 7) or (((not AVvvv) and $0F) shl 3)
             or (Ord(AL256) shl 2) or PP;
    CBEmit(ACB, $C5);
    CBEmit(ACB, Byte2 and $FF);
  end
  else
  begin
    { 3-byte VEX (C4).  Byte2 = ~R<<7|~X<<6|~B<<5|map ; Byte3 = W<<7|~vvvv<<3|L<<2|pp }
    Byte2 := ((1 - R) shl 7) or ((1 - X) shl 6) or ((1 - B) shl 5) or (AMap and $1F);
    Byte3 := (Ord(AW) shl 7) or (((not AVvvv) and $0F) shl 3)
             or (Ord(AL256) shl 2) or PP;
    CBEmit(ACB, $C4);
    CBEmit(ACB, Byte2 and $FF);
    CBEmit(ACB, Byte3 and $FF);
  end;
  CBEmit(ACB, AOpcode);
  CBEmit(ACB, MakeModRM(3, ADstReg, ARmReg));
end;

{ As EmitVexRR but the r/m operand is memory. }
procedure EmitVexRM(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  APrefix, AMap: Integer; AW, AL256: Boolean;
  AOpcode, ADstReg, AVvvv: Integer; const AMem: TOperand);
var
  R, X, B, PP, Byte2, Byte3, BaseReg: Integer;
begin
  BaseReg := AMem.Base;
  if BaseReg < 0 then BaseReg := 0;
  R := Ord(ADstReg >= 8);
  X := Ord(AMem.Index >= 8);
  B := Ord(BaseReg >= 8);
  PP := VexPP(APrefix);

  if (AMap = 1) and (not AW) and (X = 0) and (B = 0) then
  begin
    Byte2 := ((1 - R) shl 7) or (((not AVvvv) and $0F) shl 3)
             or (Ord(AL256) shl 2) or PP;
    CBEmit(ACB, $C5);
    CBEmit(ACB, Byte2 and $FF);
  end
  else
  begin
    Byte2 := ((1 - R) shl 7) or ((1 - X) shl 6) or ((1 - B) shl 5) or (AMap and $1F);
    Byte3 := (Ord(AW) shl 7) or (((not AVvvv) and $0F) shl 3)
             or (Ord(AL256) shl 2) or PP;
    CBEmit(ACB, $C4);
    CBEmit(ACB, Byte2 and $FF);
    CBEmit(ACB, Byte3 and $FF);
  end;
  CBEmit(ACB, AOpcode);
  EncodeMemOperand(ACB, ACtx, AMem, ADstReg and 7);
end;

{ ---- SSE/FP helpers -------------------------------------------------- }

procedure EmitSSERegReg(var ACB: TCodeBuf; APrefix: Integer;
  ANeedRexW: Boolean; AOpcode1: Integer; AOpcode2: Integer;
  ASrcReg: Integer; ADstReg: Integer);
begin
  if APrefix > 0 then CBEmit(ACB, APrefix);
  if ANeedRexW then
    CBEmit(ACB, MakeRex(True, ADstReg >= 8, False, ASrcReg >= 8))
  else if (ADstReg >= 8) or (ASrcReg >= 8) then
    CBEmit(ACB, MakeRex(False, ADstReg >= 8, False, ASrcReg >= 8));
  CBEmit(ACB, $0F);
  CBEmit(ACB, AOpcode1);
  if AOpcode2 >= 0 then CBEmit(ACB, AOpcode2);
  CBEmit(ACB, MakeModRM(3, ADstReg, ASrcReg));
end;

procedure EmitSSERegMem(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  APrefix: Integer; ANeedRexW: Boolean; AOpcode1: Integer; AOpcode2: Integer;
  ARegCode: Integer; const AMem: TOperand);
var
  BaseReg: Integer;
begin
  BaseReg := AMem.Base;
  if BaseReg < 0 then BaseReg := 0;
  if APrefix > 0 then CBEmit(ACB, APrefix);
  if ANeedRexW or (ARegCode >= 8) or (BaseReg >= 8) or (AMem.Index >= 8) then
    CBEmit(ACB, MakeRex(ANeedRexW, ARegCode >= 8, AMem.Index >= 8,
                        BaseReg >= 8));
  CBEmit(ACB, $0F);
  CBEmit(ACB, AOpcode1);
  if AOpcode2 >= 0 then CBEmit(ACB, AOpcode2);
  EncodeMemOperand(ACB, ACtx, AMem, ARegCode and 7);
end;

{ ---- SSE/FP instruction encoder -------------------------------------- }

function EncodeSSE(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  Prefix: Integer;
  Opcode1, Opcode2: Integer;
  NeedRexW: Boolean;
begin
  Prefix := 0;
  Opcode1 := 0;
  Opcode2 := -1;
  NeedRexW := False;

  { Map mnemonic to prefix + opcode }
  if AMnem = 'movsd' then begin Prefix := $F2; Opcode1 := $10; end
  else if AMnem = 'movss' then begin Prefix := $F3; Opcode1 := $10; end
  else if AMnem = 'movapd' then begin Prefix := $66; Opcode1 := $28; end
  else if AMnem = 'movaps' then begin Prefix := 0; Opcode1 := $28; end
  else if AMnem = 'addsd' then begin Prefix := $F2; Opcode1 := $58; end
  else if AMnem = 'addss' then begin Prefix := $F3; Opcode1 := $58; end
  else if AMnem = 'subsd' then begin Prefix := $F2; Opcode1 := $5C; end
  else if AMnem = 'subss' then begin Prefix := $F3; Opcode1 := $5C; end
  else if AMnem = 'mulsd' then begin Prefix := $F2; Opcode1 := $59; end
  else if AMnem = 'mulss' then begin Prefix := $F3; Opcode1 := $59; end
  else if AMnem = 'divsd' then begin Prefix := $F2; Opcode1 := $5E; end
  else if AMnem = 'divss' then begin Prefix := $F3; Opcode1 := $5E; end
  else if AMnem = 'sqrtsd' then begin Prefix := $F2; Opcode1 := $51; end
  else if AMnem = 'sqrtss' then begin Prefix := $F3; Opcode1 := $51; end
  else if AMnem = 'ucomisd' then begin Prefix := $66; Opcode1 := $2E; end
  else if AMnem = 'ucomiss' then begin Prefix := 0; Opcode1 := $2E; end
  else if AMnem = 'xorpd' then begin Prefix := $66; Opcode1 := $57; end
  else if AMnem = 'xorps' then begin Prefix := 0; Opcode1 := $57; end
  else if AMnem = 'cvtsd2ss' then begin Prefix := $F2; Opcode1 := $5A; end
  else if AMnem = 'cvtss2sd' then begin Prefix := $F3; Opcode1 := $5A; end
  else if AMnem = 'cvtsi2sdq' then begin Prefix := $F2; Opcode1 := $2A; NeedRexW := True; end
  else if AMnem = 'cvtsi2ssq' then begin Prefix := $F3; Opcode1 := $2A; NeedRexW := True; end
  else if AMnem = 'cvtsd2si' then begin Prefix := $F2; Opcode1 := $2D; NeedRexW := True; end
  else if AMnem = 'cvtss2si' then begin Prefix := $F3; Opcode1 := $2D; NeedRexW := True; end
  else if AMnem = 'cvttsd2si' then begin Prefix := $F2; Opcode1 := $2C; NeedRexW := True; end
  else if AMnem = 'cvttss2si' then begin Prefix := $F3; Opcode1 := $2C; NeedRexW := True; end
  { ---- SSE2 packed-integer (128-bit xmm) ---- }
  else if AMnem = 'pxor'    then begin Prefix := $66; Opcode1 := $EF; end
  else if AMnem = 'movdqa'  then begin Prefix := $66; Opcode1 := $6F; end
  else if AMnem = 'movdqu'  then begin Prefix := $F3; Opcode1 := $6F; end
  else if AMnem = 'paddb'   then begin Prefix := $66; Opcode1 := $FC; end
  else if AMnem = 'pcmpgtb' then begin Prefix := $66; Opcode1 := $64; end
  else if AMnem = 'pcmpeqb' then begin Prefix := $66; Opcode1 := $74; end
  else if AMnem = 'psadbw'  then begin Prefix := $66; Opcode1 := $F6; end
  { 3-byte 0F 38 map. }
  else if AMnem = 'pabsb'   then begin Prefix := $66; Opcode1 := $38; Opcode2 := $1C; end
  else
    raise EAssembler.Create('SSE: unhandled mnemonic: ' + AMnem);

  { movsd/movss: store direction uses opcode $11 instead of $10 }
  if ((AMnem = 'movsd') or (AMnem = 'movss')) and
     (ASrc.Kind = opReg) and IsMemLike(ADst) then
  begin
    Opcode1 := $11;
    EmitSSERegMem(ACB, ACtx, Prefix, NeedRexW, Opcode1, Opcode2,
                  ASrc.Reg, ADst);
    Result := ACB.Data;
    Exit;
  end;

  if ((AMnem = 'movapd') or (AMnem = 'movaps')) and
     (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
  begin
    Opcode1 := $29;
    EmitSSERegReg(ACB, Prefix, NeedRexW, Opcode1, Opcode2,
                  ADst.Reg, ASrc.Reg);
    Result := ACB.Data;
    Exit;
  end;

  if (ASrc.Kind = opReg) and (ADst.Kind = opReg) then
  begin
    EmitSSERegReg(ACB, Prefix, NeedRexW, Opcode1, Opcode2,
                  ASrc.Reg, ADst.Reg);
    Result := ACB.Data;
    Exit;
  end;

  if IsMemLike(ASrc) and (ADst.Kind = opReg) then
  begin
    EmitSSERegMem(ACB, ACtx, Prefix, NeedRexW, Opcode1, Opcode2,
                  ADst.Reg, ASrc);
    Result := ACB.Data;
    Exit;
  end;

  if (ASrc.Kind = opReg) and IsMemLike(ADst) then
  begin
    EmitSSERegMem(ACB, ACtx, Prefix, NeedRexW, Opcode1, Opcode2,
                  ASrc.Reg, ADst);
    Result := ACB.Data;
    Exit;
  end;

  raise EAssembler.Create(AMnem + ': unsupported operand combination');
end;

{ ---- VEX/AVX2 instruction encoder ----------------------------------- }

function EncodeVEX(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const AOp1, AOp2, AOp3: TOperand): string;
var
  Prefix, Map, Opc: Integer;
  W, L: Boolean;
  ShiftSub: Integer;   { /n in ModRM.reg for the imm-shift forms, else -1 }
begin
  { vzeroupper: C5 F8 77, no operands (vvvv=1111, L=0, pp=0). }
  if AMnem = 'vzeroupper' then
  begin
    CBEmit(ACB, $C5); CBEmit(ACB, $F8); CBEmit(ACB, $77);
    Result := ACB.Data;
    Exit;
  end;

  { VEX.L: 256-bit (ymm) vs 128-bit (xmm), taken from a vector register
    operand's width (ymm = 256).  Prefer the destination (last operand); fall
    back to an earlier vector operand. }
  if (AOp3.Kind = opReg) and (AOp3.RegW = 256) then L := True
  else if (AOp3.Kind = opReg) and (AOp3.RegW = 128) then L := False
  else if (AOp2.Kind = opReg) and (AOp2.RegW = 256) then L := True
  else if (AOp1.Kind = opReg) and (AOp1.RegW = 256) then L := True
  else L := False;

  Prefix := 0; Map := 1; W := False; ShiftSub := -1; Opc := 0;

  if AMnem = 'vpxor'    then begin Prefix := $66; Opc := $EF; end
  else if AMnem = 'vpaddb'   then begin Prefix := $66; Opc := $FC; end
  else if AMnem = 'vpaddw'   then begin Prefix := $66; Opc := $FD; end
  else if AMnem = 'vpaddq'   then begin Prefix := $66; Opc := $D4; end
  else if AMnem = 'vpcmpeqb' then begin Prefix := $66; Opc := $74; end
  else if AMnem = 'vpcmpgtb' then begin Prefix := $66; Opc := $64; end
  else if AMnem = 'vpsadbw'  then begin Prefix := $66; Opc := $F6; end
  else if AMnem = 'vpabsb'   then begin Prefix := $66; Map := 2; Opc := $1C; end
  else if AMnem = 'vmovdqa'  then begin Prefix := $66; Opc := $6F; end
  else if AMnem = 'vmovdqu'  then begin Prefix := $F3; Opc := $6F; end
  else if AMnem = 'vpsllw'   then begin Prefix := $66; Opc := $71; ShiftSub := 6; end
  else if AMnem = 'vpsrlw'   then begin Prefix := $66; Opc := $71; ShiftSub := 2; end
  else if AMnem = 'vpshufd'  then begin Prefix := $66; Opc := $70; end
  else if AMnem = 'vextracti128' then begin Prefix := $66; Map := 3; Opc := $39; end
  else if AMnem = 'vmovd' then
  begin
    { vmovd %xmm, %r32 : 66 VEX.128.0F.W0 7E /r — gp reg in r/m, xmm in reg. }
    EmitVexRR(ACB, $66, 1, False, False, $7E, AOp1.Reg, 0, AOp2.Reg);
    Result := ACB.Data;
    Exit;
  end
  else
    raise EAssembler.Create('VEX: unhandled mnemonic: ' + AMnem);

  { Imm-shift forms: vpsllw $imm, src, dst.  ModRM.reg = /ShiftSub, r/m = src,
    vvvv = dst; imm8 trails. }
  if ShiftSub >= 0 then
  begin
    if (AOp1.Kind = opImm) and (AOp2.Kind = opReg) and (AOp3.Kind = opReg) then
    begin
      EmitVexRR(ACB, Prefix, Map, W, L, Opc, ShiftSub, AOp3.Reg, AOp2.Reg);
      CBEmit(ACB, Integer(AOp1.Imm) and $FF);
    end
    else
      raise EAssembler.Create(AMnem + ': bad shift operands');
    Result := ACB.Data;
    Exit;
  end;

  { Imm + 2 regs (no vvvv): vpshufd $imm,%src,%dst ; vextracti128 $imm,%src,%dst.
    ModRM.reg = src(reg field holds the operand being read), r/m = dst, imm8
    trails, vvvv unused (1111).  Note for vextracti128 the ENCODING reg/rm
    direction is reversed vs vpshufd (it stores ymm-src in reg, xmm-dst in rm),
    and VEX.L=1 always (it operates on a 256-bit source despite the xmm dst). }
  if AMnem = 'vpshufd' then
  begin
    if (AOp1.Kind = opImm) and (AOp2.Kind = opReg) and (AOp3.Kind = opReg) then
    begin
      EmitVexRR(ACB, Prefix, Map, W, L, Opc, AOp3.Reg, 0, AOp2.Reg);
      CBEmit(ACB, Integer(AOp1.Imm) and $FF);
    end
    else
      raise EAssembler.Create(AMnem + ': bad operands');
    Result := ACB.Data;
    Exit;
  end;

  if AMnem = 'vextracti128' then
  begin
    if (AOp1.Kind = opImm) and (AOp2.Kind = opReg) and (AOp3.Kind = opReg) then
    begin
      { ymm src is in ModRM.reg, xmm dst in r/m; L=1 (256-bit source). }
      EmitVexRR(ACB, Prefix, Map, W, True, Opc, AOp2.Reg, 0, AOp3.Reg);
      CBEmit(ACB, Integer(AOp1.Imm) and $FF);
    end
    else
      raise EAssembler.Create(AMnem + ': bad operands');
    Result := ACB.Data;
    Exit;
  end;

  { Two-operand (no vvvv): vpabsb %src,%dst ; vmovdqa/vmovdqu %src/mem,%dst. }
  if AOp3.Kind = opNone then
  begin
    if (AOp1.Kind = opReg) and (AOp2.Kind = opReg) then
      EmitVexRR(ACB, Prefix, Map, W, L, Opc, AOp2.Reg, 0, AOp1.Reg)
    else if IsMemLike(AOp1) and (AOp2.Kind = opReg) then
      EmitVexRM(ACB, ACtx, Prefix, Map, W, L, Opc, AOp2.Reg, 0, AOp1)
    else
      raise EAssembler.Create(AMnem + ': bad 2-operand form');
    Result := ACB.Data;
    Exit;
  end;

  { Three-operand: vpaddb %src2,%src1,%dst.  ModRM.reg = dst, vvvv = src1,
    r/m = src2 (reg or mem). }
  if (AOp1.Kind = opReg) and (AOp2.Kind = opReg) and (AOp3.Kind = opReg) then
    EmitVexRR(ACB, Prefix, Map, W, L, Opc, AOp3.Reg, AOp2.Reg, AOp1.Reg)
  else if IsMemLike(AOp1) and (AOp2.Kind = opReg) and (AOp3.Kind = opReg) then
    EmitVexRM(ACB, ACtx, Prefix, Map, W, L, Opc, AOp3.Reg, AOp2.Reg, AOp1)
  else
    raise EAssembler.Create(AMnem + ': bad 3-operand form');
  Result := ACB.Data;
end;

{ Encode `movq`/`movd` moving between an XMM register and a GP register or
  memory.  The XMM operand is always the ModRM.reg field:
    xmm <- gp/mem :  66 [REX.W] 0F 6E /r   (load into xmm)
    gp/mem <- xmm :  66 [REX.W] 0F 7E /r   (store from xmm)
  REX.W is set for movq (64-bit), clear for movd (32-bit).  This is the path the
  generic integer mov cannot encode (it would treat %xmm0 as %rax). }
function EncodeMovqXmm(var ACB: TCodeBuf; var ACtx: TEncodeContext;
  const AMnem: string; const ASrc, ADst: TOperand): string;
var
  NeedRexW: Boolean;
begin
  NeedRexW := (AMnem = 'movq');
  if ADst.IsXmm and (ASrc.Kind = opReg) and not ASrc.IsXmm then
    { gp -> xmm: opcode 6E, xmm is reg, gp is r/m. }
    EmitSSERegReg(ACB, $66, NeedRexW, $6E, -1, ASrc.Reg, ADst.Reg)
  else if ASrc.IsXmm and (ADst.Kind = opReg) and not ADst.IsXmm then
    { xmm -> gp: opcode 7E, xmm is reg, gp is r/m. }
    EmitSSERegReg(ACB, $66, NeedRexW, $7E, -1, ADst.Reg, ASrc.Reg)
  else if ADst.IsXmm and IsMemLike(ASrc) then
    { mem -> xmm: opcode 6E. }
    EmitSSERegMem(ACB, ACtx, $66, NeedRexW, $6E, -1, ADst.Reg, ASrc)
  else if ASrc.IsXmm and IsMemLike(ADst) then
    { xmm -> mem: opcode 7E. }
    EmitSSERegMem(ACB, ACtx, $66, NeedRexW, $7E, -1, ASrc.Reg, ADst)
  else
    raise EAssembler.Create(AMnem + ': unsupported xmm/gp operand combination');
  Result := ACB.Data;
end;

{ Re-raise an assembler error annotated with the source line number and
  raw line text.  Without this, failures surface with zero diagnostics. }
procedure AsmLineError(ALineNum: Integer; const ARawLine, AMsg: string);
begin
  raise EAssembler.Create('line ' + IntToStr(ALineNum) + ': ' + AMsg
    + ' [' + TrimStr(ARawLine) + ']');
end;

{ ---- Directive handler ------------------------------------------------ }

procedure HandleDirective(const AParsed: TParsedLine;
  var ASection: TContainerSectionKind; AWriter: IContainerWriter;
  var AGlobals: TDictionary<string, Boolean>;
  var AWeaks: TDictionary<string, Boolean>;
  var ATypes: TDictionary<string, TContainerSymType>;
  var ACtx: TEncodeContext);
var
  Dir, Args: string;
  P: Integer;
  Val: Int64;
  Buf: string;
  I, Len: Integer;
  C: Integer;
  SymName: string;
  TypeStr: string;
  DVal: Double;
  FVal: Single;
  DataOp: TOperand;
  OpEnd: Integer;
  Count, Size, FillVal, J: Integer;
begin
  Dir := AParsed.Mnemonic;
  Args := TrimStr(AParsed.RawLine);

  if Dir = '.text' then
  begin
    ASection := cskText;
    Exit;
  end;

  if Dir = '.data' then
  begin
    ASection := cskData;
    Exit;
  end;

  if (Dir = '.section') then
  begin
    if StartsWithStr(Args, '.rodata') then
      ASection := cskRodata
    else if StartsWithStr(Args, '.tbss') then
      ASection := cskTbss
    else if StartsWithStr(Args, '.note.GNU-stack') then
      Exit
    else if StartsWithStr(Args, '.data') then
      ASection := cskData
    else if StartsWithStr(Args, '.bss') then
      ASection := cskBss
    else if StartsWithStr(Args, '.opdf') then
      { OPDF debug section: alloc+write progbits data.  Holds .byte/.word/.int/
        .quad/.ascii records emitted by uDebugOPDF; .quad <label> lines become
        R_X86_64_64 relocations via the same data-section machinery below. }
      ASection := cskOpdf
    else
      raise EAssembler.Create('unsupported section: ' + Args);
    Exit;
  end;

  if Dir = '.globl' then
  begin
    SymName := TrimStr(Args);
    if not AGlobals.ContainsKey(SymName) then
      AGlobals.Add(SymName, True);
    Exit;
  end;

  if Dir = '.weak' then
  begin
    SymName := TrimStr(Args);
    if not AWeaks.ContainsKey(SymName) then
      AWeaks.Add(SymName, True);
    Exit;
  end;

  if Dir = '.type' then
  begin
    P := Pos(',', Args);
    if P >= 0 then
    begin
      SymName := TrimStr(Copy(Args, 0, P));
      TypeStr := TrimStr(Copy(Args, P + 1, Length(Args) - P - 1));
      if (TypeStr = '@function') then
      begin
        if not ATypes.ContainsKey(SymName) then
          ATypes.Add(SymName, cstFunc);
      end
      else if (TypeStr = '@object') then
      begin
        if not ATypes.ContainsKey(SymName) then
          ATypes.Add(SymName, cstObject);
      end
      else if (TypeStr = '@tls_object') then
      begin
        if not ATypes.ContainsKey(SymName) then
          ATypes.Add(SymName, cstTLS);
      end;
    end;
    Exit;
  end;

  if Dir = '.balign' then
  begin
    P := 0;
    Val := ParseInt(Args, P);
    AWriter.AlignSection(ASection, Integer(Val));
    Exit;
  end;

  { .byte and .word accept a comma-separated list of values, e.g.
    `.byte 79, 80, 68, 70` (the OPDF magic) or `.byte 0,0,0,...` (BuildID).
    Emit each value in order. }
  if Dir = '.byte' then
  begin
    P := 0;
    Len := Length(Args);
    while P < Len do
    begin
      while (P < Len) and ((Args[P] = Ord(' ')) or (Args[P] = Ord(#9)) or
                           (Args[P] = Ord(','))) do
        P := P + 1;
      if P >= Len then break;
      Val := ParseInt(Args, P);
      AWriter.AppendByte(ASection, Integer(Val));
    end;
    Exit;
  end;

  if Dir = '.word' then
  begin
    P := 0;
    Len := Length(Args);
    while P < Len do
    begin
      while (P < Len) and ((Args[P] = Ord(' ')) or (Args[P] = Ord(#9)) or
                           (Args[P] = Ord(','))) do
        P := P + 1;
      if P >= Len then break;
      Val := ParseInt(Args, P);
      AWriter.AppendWord(ASection, Integer(Val));
    end;
    Exit;
  end;

  { .fill <count>, <size>, <value> — emit <count> copies of a <size>-byte
    little-endian <value>.  Used for SIMD threshold constant blocks
    (e.g. `.fill 32, 1, 0xBF`).  size/value default to 1/0 if omitted (GNU as),
    but the RTL always supplies all three. }
  if Dir = '.fill' then
  begin
    P := 0;
    Len := Length(Args);
    while (P < Len) and ((Args[P] = Ord(' ')) or (Args[P] = Ord(#9))) do P := P + 1;
    Val := ParseInt(Args, P);              { count }
    Count := Integer(Val);
    Size := 1; FillVal := 0;
    while (P < Len) and ((Args[P] = Ord(' ')) or (Args[P] = Ord(#9)) or
                         (Args[P] = Ord(','))) do P := P + 1;
    if P < Len then
    begin
      Size := Integer(ParseInt(Args, P));  { size }
      while (P < Len) and ((Args[P] = Ord(' ')) or (Args[P] = Ord(#9)) or
                           (Args[P] = Ord(','))) do P := P + 1;
      if P < Len then
        FillVal := Integer(ParseInt(Args, P));  { value }
    end;
    for I := 0 to Count - 1 do
      for J := 0 to Size - 1 do
        AWriter.AppendByte(ASection, (FillVal shr (J * 8)) and $FF);
    Exit;
  end;

  { .int is an alias for .long: GNU as treats both as a 32-bit value on
    x86-64.  The OPDF debug emitter uses .int, so accept it here. }
  if (Dir = '.long') or (Dir = '.int') then
  begin
    DataOp := ParseOperand(Args, 0, OpEnd);
    if DataOp.Kind = opLabel then
    begin
      { .long <symbol>[+disp] — absolute 32-bit address, filled in by
        the linker via R_X86_64_32. }
      ACtx.Section := ASection;
      AddRelocReq(ACtx, AWriter.CurrentOffset(ASection), DataOp.Sym,
                  crk32, DataOp.SymDisp);
      AWriter.AppendDWord(ASection, 0);
    end
    else if DataOp.Kind = opImm then
      AWriter.AppendDWord(ASection, Integer(DataOp.Imm))
    else
      raise EAssembler.Create('.long: unsupported operand: ' + Args);
    Exit;
  end;

  if Dir = '.quad' then
  begin
    DataOp := ParseOperand(Args, 0, OpEnd);
    if DataOp.Kind = opLabel then
    begin
      { .quad <symbol>[+disp] — absolute 64-bit address (vtables,
        typeinfo, class-name records), filled in by the linker via
        R_X86_64_64.  Silently emitting zero here corrupts every
        vtable in the program. }
      ACtx.Section := ASection;
      AddRelocReq(ACtx, AWriter.CurrentOffset(ASection), DataOp.Sym,
                  crk64, DataOp.SymDisp);
      AWriter.AppendQWord(ASection, 0);
    end
    else if DataOp.Kind = opImm then
      AWriter.AppendQWord(ASection, DataOp.Imm)
    else
      raise EAssembler.Create('.quad: unsupported operand: ' + Args);
    Exit;
  end;

  if Dir = '.double' then
  begin
    DVal := _StrToDouble(PChar(Args));
    Val := DoubleBits(DVal);
    AWriter.AppendDWord(ASection, Integer(Val and $FFFFFFFF));
    AWriter.AppendDWord(ASection, Integer((Val shr 32) and $FFFFFFFF));
    Exit;
  end;

  if Dir = '.float' then
  begin
    DVal := _StrToDouble(PChar(Args));
    FVal := Single(DVal);
    AWriter.AppendDWord(ASection, SingleBits(FVal));
    Exit;
  end;

  if Dir = '.ascii' then
  begin
    { Parse a quoted string }
    Buf := '';
    P := Pos('"', Args);
    if P >= 0 then
    begin
      I := P + 1;
      Len := Length(Args);
      while I < Len do
      begin
        C := Args[I];
        if C = Ord('"') then break;
        if C = '\' then
        begin
          I := I + 1;
          if I < Len then
          begin
            C := Args[I];
            if C = Ord('n') then Buf := Buf + #10
            else if C = Ord('t') then Buf := Buf + #9
            else if C = Ord('r') then Buf := Buf + #13
            { NOTE: no '\0' shortcut here.  It must fall through to the octal
              branch below, or a zero-padded escape like '\000' followed by a
              digit-or-letter is mis-parsed: '\0' would consume just the first
              zero and the remaining "00b" would be copied through as literal
              characters.  gas caps an octal escape at three digits, and the
              octal branch below matches that, so '\000' is exactly one NUL. }
            else if C = '\' then Buf := Buf + '\'
            else if C = Ord('"') then Buf := Buf + '"'
            else if (C = Ord('x')) or (C = Ord('X')) then
            begin
              { Hex escape: \xHH — 1 or 2 hex digits }
              Val := 0;
              if (I + 1 < Len) and IsHexDigit(Args[I + 1]) then
              begin
                I := I + 1;
                C := Args[I];
                if IsDigit(C) then Val := Ord(C) - Ord('0')
                else if (C >= Ord('a')) and (C <= Ord('f')) then Val := 10 + Ord(C) - Ord('a')
                else Val := 10 + Ord(C) - Ord('A');
                if (I + 1 < Len) and IsHexDigit(Args[I + 1]) then
                begin
                  I := I + 1;
                  C := Args[I];
                  Val := Val * 16;
                  if IsDigit(C) then Val := Val + Ord(C) - Ord('0')
                  else if (C >= Ord('a')) and (C <= Ord('f')) then Val := Val + 10 + Ord(C) - Ord('a')
                  else Val := Val + 10 + Ord(C) - Ord('A');
                end;
              end;
              Buf := Buf + Chr(Integer(Val));
            end
            else if IsDigit(C) then
            begin
              { Octal escape }
              Val := Ord(C) - Ord('0');
              if (I + 1 < Len) and IsDigit(Args[I + 1]) then
              begin
                I := I + 1;
                Val := Val * 8 + (Ord(Args[I]) - Ord('0'));
                if (I + 1 < Len) and IsDigit(Args[I + 1]) then
                begin
                  I := I + 1;
                  Val := Val * 8 + (Ord(Args[I]) - Ord('0'));
                end;
              end;
              Buf := Buf + Chr(Integer(Val));
            end
            else
              Buf := Buf + Chr(C);
          end;
        end
        else
          Buf := Buf + Chr(C);
        I := I + 1;
      end;
    end;
    AWriter.Append(ASection, Buf);
    Exit;
  end;

  if Dir = '.skip' then
  begin
    P := 0;
    Val := ParseInt(Args, P);
    AWriter.AppendZeros(ASection, Integer(Val));
    Exit;
  end;

  if Dir = '.p2align' then
  begin
    P := 0;
    Val := ParseInt(Args, P);
    AWriter.AlignSection(ASection, 1 shl Integer(Val));
    Exit;
  end;

  { Directives with no effect on the object file — safe to ignore. }
  if (Dir = '.file') or (Dir = '.size') or (Dir = '.ident') then
    Exit;

  { Fail loudly on anything else — a silently dropped directive is
    silent data corruption waiting to happen. }
  raise EAssembler.Create('unknown directive: ' + Dir);
end;

{ ---- Two-pass assembler driver ---------------------------------------- }

procedure SplitLines(const AText: string; ALines: TList<string>);
var
  I, Start, Len: Integer;
  C: Integer;
begin
  Len := Length(AText);
  Start := 0;
  I := 0;
  while I < Len do
  begin
    C := AText[I];
    if C = #10 then
    begin
      ALines.Add(Copy(AText, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  if Start < Len then
    ALines.Add(Copy(AText, Start, Len - Start));
end;

function DoAssemble(const AAsmText: string): string;
var
  Lines: TList<string>;
  Parsed: array of TParsedLine;
  ParsedCount: Integer;
  Labels: TLabelMap;
  Globals: TDictionary<string, Boolean>;
  Weaks: TDictionary<string, Boolean>;
  Types: TDictionary<string, TContainerSymType>;
  Writer: IContainerWriter;
  I: Integer;
  PL: TParsedLine;
  Section: TContainerSectionKind;
  Info: TLabelInfo;
  Ctx: TEncodeContext;
  Encoded: string;
  R: TRelocRequest;
  SymIdx: Integer;
  Bind: TContainerSymBind;
  SType: TContainerSymType;
  LabelKey: string;
  LabelVal: TLabelInfo;
begin
  Lines := TList<string>.Create();
  SetLength(Parsed, 0);
  ParsedCount := 0;
  Labels := TLabelMap.Create();
  Globals := TDictionary<string, Boolean>.Create();
  Weaks := TDictionary<string, Boolean>.Create();
  Types := TDictionary<string, TContainerSymType>.Create();
  Writer := TElfObjectWriter.Create();
  SetLength(Ctx.Relocs, 0);
  Ctx.RelocCount := 0;
  try
    SplitLines(AAsmText, Lines);

    { Parse all lines into dynamic array }
    SetLength(Parsed, Lines.Count);
    for I := 0 to Lines.Count - 1 do
    begin
      try
        PL := ParseLine(Lines.Get(I), I + 1);
      except
        on E: EAssembler do
          AsmLineError(I + 1, Lines.Get(I), E.Message);
      end;
      Parsed[I] := PL;
    end;
    ParsedCount := Lines.Count;

    { ---- Pass 1: collect labels and compute section sizes ---- }
    Section := cskText;
    Ctx.Labels := Labels;
    Ctx.Pass := 1;

    for I := 0 to ParsedCount - 1 do
    begin
      PL := Parsed[I];
      { blaise-guard: ignore BL-3002 - lkEmpty (blank/comment line) is handled by the else arm below; an empty else has no AST statement to detect. }
      case PL.Kind of
        lkLabel:
        begin
          if Labels.ContainsKey(PL.Mnemonic) then
            raise EAssembler.Create('line ' + IntToStr(PL.LineNum)
              + ': duplicate label: ' + PL.Mnemonic);
          Info.Section := Section;
          Info.Offset := Writer.CurrentOffset(Section);
          Info.Defined := True;
          Labels.Add(PL.Mnemonic, Info);
        end;

        lkDirective:
        begin
          try
            HandleDirective(PL, Section, Writer, Globals, Weaks, Types, Ctx);
          except
            on E: EAssembler do
              AsmLineError(PL.LineNum, PL.RawLine, E.Message);
          end;
        end;

        lkInstr:
        begin
          Ctx.Section := Section;
          Ctx.Offset := Writer.CurrentOffset(Section);
          try
            Encoded := EncodeInstruction(Ctx, PL);
          except
            on E: EAssembler do
              AsmLineError(PL.LineNum, PL.RawLine, E.Message);
          end;
          Writer.AppendZeros(Section, Length(Encoded));
        end;
      else
        { lkEmpty: a blank or comment-only line — nothing to assemble.  Named
          explicitly so a new TLineKind has to be considered here rather than
          silently doing nothing. }
      end;
    end;

    { ---- Reset section offsets for pass 2 ---- }
    { Reassignment releases the pass-1 writer (IContainerWriter is
      ARC-managed — no manual Free). }
    Writer := TElfObjectWriter.Create();
    SetLength(Ctx.Relocs, 0);
    Ctx.RelocCount := 0;

    { ---- Pass 2: encode with resolved labels ---- }
    Section := cskText;
    Ctx.Pass := 2;

    for I := 0 to ParsedCount - 1 do
    begin
      PL := Parsed[I];
      { blaise-guard: ignore BL-3002 - lkEmpty (blank/comment line) is handled by the else arm below; an empty else has no AST statement to detect. }
      case PL.Kind of
        lkLabel:
        begin
          Info.Section := Section;
          Info.Offset := Writer.CurrentOffset(Section);
          Info.Defined := True;
          Labels.Add(PL.Mnemonic, Info);
        end;

        lkDirective:
        begin
          try
            HandleDirective(PL, Section, Writer, Globals, Weaks, Types, Ctx);
          except
            on E: EAssembler do
              AsmLineError(PL.LineNum, PL.RawLine, E.Message);
          end;
        end;

        lkInstr:
        begin
          Ctx.Section := Section;
          Ctx.Offset := Writer.CurrentOffset(Section);
          try
            Encoded := EncodeInstruction(Ctx, PL);
          except
            on E: EAssembler do
              AsmLineError(PL.LineNum, PL.RawLine, E.Message);
          end;
          Writer.Append(Section, Encoded);
        end;
      else
        { lkEmpty: a blank or comment-only line — nothing to assemble.  Named
          explicitly so a new TLineKind has to be considered here rather than
          silently doing nothing. }
      end;
    end;

    { ---- Define symbols ---- }
    Writer.DefineSymbol('', cskText, 0, 0, csbLocal, cstSection);
    Writer.DefineSymbol('.data', cskData, 0, 0, csbLocal, cstSection);
    Writer.DefineSymbol('.rodata', cskRodata, 0, 0, csbLocal, cstSection);

    for I := 0 to Labels.Count - 1 do
    begin
      LabelKey := Labels.GetKey(I);
      LabelVal := Labels.GetVal(I);

      if Globals.ContainsKey(LabelKey) then
        Bind := csbGlobal
      else if Weaks.ContainsKey(LabelKey) then
        Bind := csbWeak
      else
        Bind := csbLocal;

      if not Types.TryGetValue(LabelKey, SType) then
      begin
        { GNU as infers STT_TLS for any symbol defined in a TLS ("T"-flagged)
          section; mirror that.  External linkers resolve @tpoff against a
          non-TLS symbol as a plain vaddr, which puts threadvars at a wild
          positive thread-pointer offset in cc-linked binaries. }
        if LabelVal.Section = cskTbss then
          SType := cstTLS
        else
          SType := cstNone;
      end;

      Writer.DefineSymbol(LabelKey, LabelVal.Section,
                          LabelVal.Offset, 0, Bind, SType);
    end;

    { ---- Apply relocations ---- }
    for I := 0 to Ctx.RelocCount - 1 do
    begin
      R := Ctx.Relocs[I];
      SymIdx := Writer.FindSymbol(R.Symbol);
      if SymIdx < 0 then
        SymIdx := Writer.ExternSymbol(R.Symbol);
      Writer.AddReloc(R.Section, R.Offset, SymIdx, R.RType, R.Addend);
    end;

    Result := Writer.Finish();
  finally
    SetLength(Ctx.Relocs, 0);
    { Writer is IContainerWriter — released by ARC at scope exit, not Free. }
    Types.Free();
    Weaks.Free();
    Globals.Free();
    Labels.Free();
    SetLength(Parsed, 0);
    Lines.Free();
  end;
end;

procedure AssembleToObject(const AAsmText: string; const AOutputPath: string);
var
  Buf: string;
  FOut: TFileOutputStream;
begin
  Buf := DoAssemble(AAsmText);
  FOut := TFileOutputStream.Create(AOutputPath);
  try
    FOut.Write(PChar(Buf), Length(Buf));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

function AssembleToBytes(const AAsmText: string): string;
begin
  Result := DoAssemble(AAsmText);
end;

end.
