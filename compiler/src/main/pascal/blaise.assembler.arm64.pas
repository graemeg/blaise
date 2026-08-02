{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.assembler.arm64;

{ Self-assembler for the AArch64 backend's GNU-syntax assembly dialect —
  the arm64 sibling of blaise.assembler.x86_64 (macos-arm64 Phase 1b,
  docs/macos-arm64-backend-design.adoc).

  Parses the restricted AArch64 subset the (coming) TArm64Backend emits
  and encodes it into a Mach-O MH_OBJECT via the IContainerWriter seam
  (TMachOObjectWriter).  There is NO external fallback: Linux binutils
  cannot assemble Mach-O arm64, so this component gates all macOS
  cross-compilation.

  A64 instructions are fixed 4-byte words, so the two-pass model is
  simpler than x86-64: pass 1 collects labels (every instruction is
  exactly 4 bytes), pass 2 encodes with resolved label offsets.

  Branches to labels defined in the same file resolve to PC-relative
  immediates; branches to undefined symbols emit ARM64_RELOC_BRANCH26.
  adrp/add/ldr with @PAGE/@PAGEOFF/@GOTPAGE/@GOTPAGEOFF/@TLVPPAGE/
  @TLVPPAGEOFF operands emit the matching ARM64_RELOC_* with a zero
  immediate for the linker/loader to fill. }

interface

uses
  SysUtils, Generics.Collections, blaise.container.writer,
  blaise.machowriter;

type
  EArm64Assembler = class(Exception);

{ Assemble AArch64 text to MH_OBJECT bytes. }
function AssembleArm64ToBytes(const AAsmText: string): string;
{ Assemble and write to a file. }
procedure AssembleArm64ToObject(const AAsmText: string;
  const AOutputPath: string; const AIfaceBytes: string);

implementation

uses
  streams, uStrCompat;

type
  TSymRef = (srNone, srPage, srPageOff, srGotPage, srGotPageOff,
             srTlvPage, srTlvPageOff);

  TA64OpKind = (okNone, okReg, okImm, okMem, okSym, okFImm);

  TA64Op = record
    Kind:     TA64OpKind;
    Reg:      Integer;   { 0..31; 31 = sp or zr per context }
    Is64:     Boolean;   { x/d vs w/s }
    IsFP:     Boolean;
    IsSP:     Boolean;   { named sp (vs xzr, both encode 31) }
    Imm:      Int64;
    Base:     Integer;   { mem: base register }
    MemImm:   Int64;     { mem: offset }
    PreIdx:   Boolean;   { [xN, #i]! }
    PostIdx:  Boolean;   { [xN], #i }
    Sym:      string;
    SymRef:   TSymRef;
    MemSym:   string;    { mem: [xN, sym@PAGEOFF] }
    MemSymRef: TSymRef;
  end;

  TLineKind = (alBlank, alLabel, alDirective, alInstr);

  TA64Line = record
    Kind:     TLineKind;
    Mnemonic: string;    { lowercased mnemonic or directive }
    Cond:     string;    { b.<cond> condition part }
    Args:     string;    { raw operand text }
    RawLine:  string;
    LineNum:  Integer;
  end;

  TLabelInfo = record
    Section: TContainerSectionKind;
    Offset:  Integer;
  end;

  { The assembler as a class: shared state lives in fields and the encode
    helpers are methods — deliberately NOT nested procedures, because
    sibling nested-routine calls do not forward captures (BUG-031) and
    interface-typed captures are unsupported (BUG-038); both shapes
    crashed here before the class conversion. }
  TArm64Assembler = class
  private
    FW: TMachOObjectWriter;
    FSection: TContainerSectionKind;
    FPassNo: Integer;
    { two parallel maps, not TDictionary<string, RECORD> — a record value
      type in a generic dictionary instance crashed at runtime (candidate
      new bug; minimise separately) }
    FLabelSec: TDictionary<string, Integer>;   { Ord(section kind) }
    FLabelOff: TDictionary<string, Integer>;
    FGlobals: TDictionary<string, Boolean>;
    FWeaks: TDictionary<string, Boolean>;
    FCurOff: Integer;
    FL: TA64Line;
    FA: array of TA64Op;
    FNOps: Integer;
    procedure EmitW(AVal: Integer);
    procedure LineError(const AMsg: string);
    function BranchDelta(const ASym: string; AKind: TContainerRelocKind;
      out AIsLocal: Boolean): Integer;
    procedure SymReloc(const ASym: string; ARef: TSymRef);
    procedure NeedOps(AN: Integer);
    procedure HandleDirective;
    procedure EncodeInstr;
  public
    { When non-empty, the object gains a (__BLAISE,__blaise_iface) section
      holding these bytes — the unit's .bif, so an .o carries its own interface
      and a consumer can import it with the source gone.  Set before Assemble. }
    IfacePayload: string;
    function Assemble(const AAsmText: string): string;
  end;

const
  CondNames: array[0..15] of string = (
    'eq','ne','cs','cc','mi','pl','vs','vc',
    'hi','ls','ge','lt','gt','le','al','nv');

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

function CondCode(const AName: string): Integer;
var
  I: Integer;
begin
  for I := 0 to 15 do
    if CondNames[I] = AName then
    begin
      Result := I;
      Exit;
    end;
  { aliases }
  if AName = 'hs' then Exit(2);
  if AName = 'lo' then Exit(3);
  raise EArm64Assembler.Create('unknown condition: ' + AName);
end;

{ Invert a condition code (cset lowers to csinc with the inverse). }
function CondInvert(ACode: Integer): Integer;
begin
  Result := ACode xor 1;
end;

{ ---- lexing helpers ---------------------------------------------------- }

function IsSpaceC(C: Integer): Boolean;
begin
  Result := (C = 32) or (C = 9);
end;

function TrimS(const S: string): string;
var
  A, B: Integer;
begin
  A := 0;
  B := Length(S) - 1;
  while (A <= B) and IsSpaceC(StrAt(S, A)) do A := A + 1;
  while (B >= A) and IsSpaceC(StrAt(S, B)) do B := B - 1;
  Result := Copy(S, A, B - A + 1);
end;

function LowerS(const S: string): string;
begin
  Result := LowerCase(S);
end;

{ Split ATxt on top-level commas (not inside [] brackets). }
procedure SplitOperands(const ATxt: string; AOut: TList<string>);
var
  I, Depth, Start, C: Integer;
begin
  Depth := 0;
  Start := 0;
  for I := 0 to Length(ATxt) - 1 do
  begin
    C := StrAt(ATxt, I);
    if C = Ord('[') then Depth := Depth + 1
    else if C = Ord(']') then Depth := Depth - 1
    else if (C = Ord(',')) and (Depth = 0) then
    begin
      AOut.Add(TrimS(Copy(ATxt, Start, I - Start)));
      Start := I + 1;
    end;
  end;
  if TrimS(Copy(ATxt, Start, Length(ATxt) - Start)) <> '' then
    AOut.Add(TrimS(Copy(ATxt, Start, Length(ATxt) - Start)));
end;

{ Parse a register name.  Returns True and fills the fields on match. }
function TryParseReg(const S: string; out AReg: Integer; out AIs64: Boolean;
  out AIsFP: Boolean; out AIsSP: Boolean): Boolean;
var
  N: Integer;
  Body: string;
begin
  Result := False;
  AIsSP := False;
  AIsFP := False;
  if S = '' then Exit;
  if (S = 'sp') then
  begin
    AReg := 31; AIs64 := True; AIsSP := True;
    Result := True; Exit;
  end;
  if (S = 'xzr') then begin AReg := 31; AIs64 := True; Result := True; Exit; end;
  if (S = 'wzr') then begin AReg := 31; AIs64 := False; Result := True; Exit; end;
  if (S = 'fp') then begin AReg := 29; AIs64 := True; Result := True; Exit; end;
  if (S = 'lr') then begin AReg := 30; AIs64 := True; Result := True; Exit; end;
  Body := Copy(S, 1, Length(S) - 1);
  if Body = '' then Exit;
  N := StrToIntDef(Body, -1);
  if (N < 0) or (N > 31) then Exit;
  case StrAt(S, 0) of
    Ord('x'): begin AReg := N; AIs64 := True;  end;
    Ord('w'): begin AReg := N; AIs64 := False; end;
    Ord('d'): begin AReg := N; AIs64 := True;  AIsFP := True; end;
    Ord('s'): begin AReg := N; AIs64 := False; AIsFP := True; end;
  else
    Exit;
  end;
  Result := True;
end;

function ParseImmediate(const S: string): Int64;
var
  T: string;
begin
  T := S;
  if (Length(T) > 0) and (StrAt(T, 0) = Ord('#')) then
    T := Copy(T, 1, Length(T) - 1);
  if (Length(T) > 1) and (StrAt(T, 0) = Ord('0')) and
     ((StrAt(T, 1) = Ord('x')) or (StrAt(T, 1) = Ord('X'))) then
    Result := StrToInt64('$' + Copy(T, 2, Length(T) - 2))
  else
    Result := StrToInt64(T);
end;

{ Split 'name@SUFFIX' into symbol + reference kind. }
procedure ParseSymRef(const S: string; out ASym: string; out ARef: TSymRef);
var
  P: Integer;
  Suf: string;
begin
  P := Pos('@', S);
  if P < 0 then
  begin
    ASym := S;
    ARef := srNone;
    Exit;
  end;
  ASym := Copy(S, 0, P);
  Suf := UpperCase(Copy(S, P + 1, Length(S) - P - 1));
  if Suf = 'PAGE' then ARef := srPage
  else if Suf = 'PAGEOFF' then ARef := srPageOff
  else if Suf = 'GOTPAGE' then ARef := srGotPage
  else if Suf = 'GOTPAGEOFF' then ARef := srGotPageOff
  else if Suf = 'TLVPPAGE' then ARef := srTlvPage
  else if Suf = 'TLVPPAGEOFF' then ARef := srTlvPageOff
  else
    raise EArm64Assembler.Create('unknown symbol suffix: @' + Suf);
end;

function SymRefToReloc(ARef: TSymRef): TContainerRelocKind;
begin
  case ARef of
    srPage:       Result := crkArm64Page21;
    srPageOff:    Result := crkArm64PageOff12;
    srGotPage:    Result := crkArm64GotPage21;
    srGotPageOff: Result := crkArm64GotPageOff12;
    srTlvPage:    Result := crkArm64TlvPage21;
    srTlvPageOff: Result := crkArm64TlvPageOff12;
  else
    raise EArm64Assembler.Create('symbol operand needs a @PAGE-family suffix');
  end;
end;

function ParseOperand(const S: string): TA64Op;
var
  R: Integer;
  Is64, IsFP, IsSP: Boolean;
  Inner, BasePart, OffPart: string;
  P: Integer;
  C0: Integer;
begin
  Result.Kind := okNone;
  Result.SymRef := srNone;
  Result.MemSymRef := srNone;
  Result.PreIdx := False;
  Result.PostIdx := False;
  Result.MemImm := 0;
  if S = '' then Exit;
  C0 := StrAt(S, 0);

  if TryParseReg(LowerS(S), R, Is64, IsFP, IsSP) then
  begin
    Result.Kind := okReg;
    Result.Reg := R;
    Result.Is64 := Is64;
    Result.IsFP := IsFP;
    Result.IsSP := IsSP;
    Exit;
  end;

  if C0 = Ord('#') then
  begin
    { float immediate only for fcmp #0.0 — detect '.' }
    if Pos('.', S) >= 0 then
    begin
      Result.Kind := okFImm;
      Result.Imm := 0;   { only #0.0 supported }
      if TrimS(Copy(S, 1, Length(S) - 1)) <> '0.0' then
        raise EArm64Assembler.Create('only #0.0 float immediate supported');
      Exit;
    end;
    Result.Kind := okImm;
    Result.Imm := ParseImmediate(S);
    Exit;
  end;

  if C0 = Ord('[') then
  begin
    { [base], [base, #imm], [base, #imm]! , [base], #imm, [base, sym@REF] }
    P := Pos(']', S);
    if P < 0 then
      raise EArm64Assembler.Create('malformed memory operand: ' + S);
    Inner := TrimS(Copy(S, 1, P - 1));
    Result.Kind := okMem;
    if P + 1 < Length(S) then
    begin
      if StrAt(S, P + 1) = Ord('!') then
        Result.PreIdx := True
      else
      begin
        { post-index: '], #imm' }
        OffPart := TrimS(Copy(S, P + 1, Length(S) - P - 1));
        if (Length(OffPart) > 0) and (StrAt(OffPart, 0) = Ord(',')) then
        begin
          Result.PostIdx := True;
          Result.MemImm := ParseImmediate(TrimS(
            Copy(OffPart, 1, Length(OffPart) - 1)));
        end;
      end;
    end;
    P := Pos(',', Inner);
    if P < 0 then
      BasePart := Inner
    else
    begin
      BasePart := TrimS(Copy(Inner, 0, P));
      OffPart := TrimS(Copy(Inner, P + 1, Length(Inner) - P - 1));
      if (OffPart <> '') and (StrAt(OffPart, 0) = Ord('#')) then
        Result.MemImm := ParseImmediate(OffPart)
      else if OffPart <> '' then
        ParseSymRef(OffPart, Result.MemSym, Result.MemSymRef);
    end;
    if not TryParseReg(LowerS(BasePart), R, Is64, IsFP, IsSP) then
      raise EArm64Assembler.Create('bad base register: ' + BasePart);
    Result.Base := R;
    Exit;
  end;

  { symbol (with optional @REF) or bare label }
  Result.Kind := okSym;
  ParseSymRef(S, Result.Sym, Result.SymRef);
end;

{ ---- line parsing ------------------------------------------------------ }

function ParseLine(const ALine: string; ANum: Integer): TA64Line;
var
  S: string;
  P, C: Integer;
  InStr: Boolean;
begin
  Result.RawLine := ALine;
  Result.LineNum := ANum;
  Result.Cond := '';
  S := ALine;
  { Strip a trailing comment (';' or '//'), but NOT a delimiter that sits
    INSIDE a quoted string — e.g. `.ascii ";"` must keep its semicolon.  Scan
    char by char, tracking string state; a backslash escapes the next char so
    an embedded `\"` does not end the string. }
  P := 0;
  InStr := False;
  while P < Length(S) do
  begin
    C := StrAt(S, P);
    if InStr then
    begin
      if C = Ord('\') then
        P := P + 1                 { skip the escaped char }
      else if C = Ord('"') then
        InStr := False;
    end
    else if C = Ord('"') then
      InStr := True
    else if C = Ord(';') then
    begin
      S := Copy(S, 0, P);
      Break;
    end
    else if (C = Ord('/')) and (P + 1 < Length(S)) and
            (StrAt(S, P + 1) = Ord('/')) then
    begin
      S := Copy(S, 0, P);
      Break;
    end;
    P := P + 1;
  end;
  S := TrimS(S);
  if S = '' then
  begin
    Result.Kind := alBlank;
    Exit;
  end;
  { A '#' that OPENS a line is a comment — GNU as accepts it, and it is also how
    cpp line markers (`# 12 "file.pas"`) look.  It can only be recognised THERE:
    on AArch64 '#' introduces an immediate (`mov x0, #5`), so treating it as a
    comment character anywhere else would eat every immediate operand.  The
    x86-64 assembler has the same rule (blaise.assembler.x86_64.pas :678); arm64
    lacked it, so any '#' line was reported as an unknown instruction and every
    --debug-opdf build failed — the OPDF companion file opens with
    '# OPDF debug companion file ...' (BUG-20260726-arm64-asm-hash-comment). }
  if StrAt(S, 0) = Ord('#') then
  begin
    Result.Kind := alBlank;
    Exit;
  end;
  if StrAt(S, Length(S) - 1) = Ord(':') then
  begin
    Result.Kind := alLabel;
    Result.Mnemonic := Copy(S, 0, Length(S) - 1);
    Exit;
  end;
  P := 0;
  while (P < Length(S)) and (not IsSpaceC(StrAt(S, P))) do P := P + 1;
  Result.Mnemonic := LowerS(Copy(S, 0, P));
  Result.Args := TrimS(Copy(S, P, Length(S) - P));
  if StrAt(S, 0) = Ord('.') then
  begin
    { 'b.cond' is an instruction, not a directive — but it starts 'b.' }
    Result.Kind := alDirective;
  end
  else
    Result.Kind := alInstr;
  { b.<cond> }
  if (Result.Kind = alInstr) and (Copy(Result.Mnemonic, 0, 2) = 'b.') then
  begin
    Result.Cond := Copy(Result.Mnemonic, 2, Length(Result.Mnemonic) - 2);
    Result.Mnemonic := 'b.cond';
  end;
end;

{ ---- encoding ----------------------------------------------------------- }

function SfBit(AIs64: Boolean): Integer;
begin
  if AIs64 then Result := 1 else Result := 0;
end;

{ add/sub immediate.  AOp: 0=add, 1=sub; ASetFlags for subs/adds/cmp/cmn. }
function EncAddSubImm(AIs64: Boolean; ASub, ASetFlags: Boolean;
  ARd, ARn: Integer; AImm: Int64): Integer;
var
  W: Integer;
  Shifted: Boolean;
begin
  { AArch64 add/sub (immediate) carries a 12-bit immediate plus an `sh` bit
    (bit 22): sh=0 means imm12, sh=1 means imm12 << 12.  Only supporting the
    unshifted form capped every add/sub at 4095, so a routine whose frame
    exceeded 4095 bytes failed to assemble outright ("add/sub immediate out of
    range: 4096") — hit by any function with a large local array (2026-07-23).
    Use the shifted form for a larger value that is a multiple of 4096. }
  Shifted := False;
  if (AImm > 4095) and ((AImm and $FFF) = 0) and (AImm <= 4095 * 4096) then
  begin
    Shifted := True;
    AImm := AImm shr 12;
  end;
  if (AImm < 0) or (AImm > 4095) then
    raise EArm64Assembler.Create('add/sub immediate out of range [0..4095]'
      + ' (or a multiple of 4096 up to 16773120): ' + IntToStr(AImm));
  W := (SfBit(AIs64) shl 31) or ($11000000);
  if ASub then W := W or (1 shl 30);
  if ASetFlags then W := W or (1 shl 29);
  if Shifted then W := W or (1 shl 22);
  Result := W or (Integer(AImm) shl 10) or (ARn shl 5) or ARd;
end;

{ add/sub shifted register (no shift). }
function EncAddSubReg(AIs64: Boolean; ASub, ASetFlags: Boolean;
  ARd, ARn, ARm: Integer): Integer;
var
  W: Integer;
begin
  W := (SfBit(AIs64) shl 31) or ($0B000000);
  if ASub then W := W or (1 shl 30);
  if ASetFlags then W := W or (1 shl 29);
  Result := W or (ARm shl 16) or (ARn shl 5) or ARd;
end;

{ add/sub EXTENDED register.  The only add/sub register form in which
  register 31 means SP rather than XZR, so it is mandatory whenever the
  destination or first source operand is sp.  Encoding: base $0B200000 (bit
  30 set for sub), option in bits 15..13 and imm3 (shift amount) in 12..10 —
  UXTX (option 3, imm3 0) is the plain 64-bit "no extension" case.

  Using the shifted-register encoder here instead assembles `sub sp, sp, x16`
  as `sub xzr, xzr, x16`: the result is discarded and sp never moves.  That
  silently broke the prologue of every function whose frame exceeds 4095
  bytes (the only ones that reserve via a register rather than an immediate),
  leaving their locals below sp to be overwritten by the next callee's
  prologue push — the macOS arm64 failure of 2026-07-23. }
function EncAddSubExtReg(AIs64: Boolean; ASub, ASetFlags: Boolean;
  ARd, ARn, ARm: Integer): Integer;
var
  W: Integer;
begin
  W := (SfBit(AIs64) shl 31) or ($0B200000);
  if ASub then W := W or (1 shl 30);
  if ASetFlags then W := W or (1 shl 29);
  { option = UXTX (3), imm3 = 0 }
  Result := W or (ARm shl 16) or (3 shl 13) or (ARn shl 5) or ARd;
end;

{ logical shifted register: and=00, orr=01, eor=10, ands=11 (opc<<29). }
function EncLogicReg(AIs64: Boolean; AOpc: Integer;
  ARd, ARn, ARm: Integer): Integer;
begin
  Result := (SfBit(AIs64) shl 31) or (AOpc shl 29) or $0A000000
    or (ARm shl 16) or (ARn shl 5) or ARd;
end;

{ madd/msub (mul = madd with ra=31). }
function EncMulAdd(AIs64: Boolean; ASubtract: Boolean;
  ARd, ARn, ARm, ARa: Integer): Integer;
var
  W: Integer;
begin
  W := (SfBit(AIs64) shl 31) or $1B000000
    or (ARm shl 16) or (ARa shl 10) or (ARn shl 5) or ARd;
  if ASubtract then W := W or (1 shl 15);
  Result := W;
end;

function EncDiv(AIs64: Boolean; ASigned: Boolean;
  ARd, ARn, ARm: Integer): Integer;
var
  W: Integer;
begin
  W := (SfBit(AIs64) shl 31) or $1AC00800 or (ARm shl 16)
    or (ARn shl 5) or ARd;
  if ASigned then W := W or (1 shl 10);   { sdiv opcode2 = 0x3, udiv 0x2 }
  Result := W;
end;

{ variable shifts: lslv op2=8, lsrv 9, asrv 10 (<<10). }
function EncShiftVar(AIs64: Boolean; AOp2: Integer;
  ARd, ARn, ARm: Integer): Integer;
begin
  Result := (SfBit(AIs64) shl 31) or $1AC00000 or (ARm shl 16)
    or (AOp2 shl 10) or (ARn shl 5) or ARd;
end;

{ ubfm/sbfm for immediate shifts. }
function EncBitfield(AIs64: Boolean; ASigned: Boolean;
  ARd, ARn, AImmR, AImmS: Integer): Integer;
var
  Base, W: Integer;
begin
  { ubfm = opc 10 ($53...), sbfm = opc 00 ($13...); N mirrors sf. }
  if ASigned then Base := $13000000 else Base := $53000000;
  W := (SfBit(AIs64) shl 31) or Base
    or (AImmR shl 16) or (AImmS shl 10) or (ARn shl 5) or ARd;
  if AIs64 then W := W or (1 shl 22);
  Result := W;
end;

{ movz/movk/movn: AOpc 2=movz, 3=movk, 0=movn. }
function EncMovWide(AIs64: Boolean; AOpc: Integer;
  ARd: Integer; AImm: Int64; AShift: Integer): Integer;
begin
  if (AImm < 0) or (AImm > $FFFF) then
    raise EArm64Assembler.Create('mov immediate out of 16-bit range');
  Result := (SfBit(AIs64) shl 31) or (AOpc shl 29) or $12800000
    or ((AShift div 16) shl 21) or (Integer(AImm) shl 5) or ARd;
end;

{ load/store register, unsigned scaled 12-bit offset.
  ASize: 0=b,1=h,2=w,3=x; AOpcBits: load/store + signedness variants. }
function EncLdStUImm(ASize: Integer; AV: Boolean; AOpc: Integer;
  ARt, ARn: Integer; AImm: Int64): Integer;
var
  Scale, W: Integer;
  Scaled: Int64;
begin
  Scale := ASize;
  if (AImm < 0) or ((AImm mod (Int64(1) shl Scale)) <> 0) then
    raise EArm64Assembler.Create('unscaled/negative load-store offset: '
      + IntToStr(AImm) + ' (use ldur/stur)');
  Scaled := AImm shr Scale;
  if Scaled > 4095 then
    raise EArm64Assembler.Create('load-store offset out of range');
  W := (ASize shl 30) or $39000000 or (AOpc shl 22)
    or (Integer(Scaled) shl 10) or (ARn shl 5) or ARt;
  if AV then W := W or (1 shl 26);
  Result := W;
end;

{ ldur/stur: unscaled signed 9-bit. }
function EncLdStUnscaled(ASize: Integer; AV: Boolean; AOpc: Integer;
  ARt, ARn: Integer; AImm: Int64): Integer;
var
  W: Integer;
begin
  if (AImm < -256) or (AImm > 255) then
    raise EArm64Assembler.Create('ldur/stur offset out of range [-256..255]');
  W := (ASize shl 30) or $38000000 or (AOpc shl 22)
    or ((Integer(AImm) and $1FF) shl 12) or (ARn shl 5) or ARt;
  if AV then W := W or (1 shl 26);
  Result := W;
end;

{ ldr/str with writeback.  APre selects pre-index ([xN, #i]!) vs
  post-index ([xN], #i); signed 9-bit immediate. }
function EncodeLdStPrePost(ASize: Integer; AV: Boolean; AOpc: Integer;
  APre: Boolean; ARt, ARn: Integer; AImm: Int64): Integer;
var
  W, Mode: Integer;
begin
  if (AImm < -256) or (AImm > 255) then
    raise EArm64Assembler.Create('pre/post-index offset out of range [-256..255]');
  if APre then Mode := 3 else Mode := 1;
  W := (ASize shl 30) or $38000000 or (AOpc shl 22)
    or ((Integer(AImm) and $1FF) shl 12) or (Mode shl 10)
    or (ARn shl 5) or ARt;
  if AV then W := W or (1 shl 26);
  Result := W;
end;

{ ldp/stp.  AMode: 0=signed offset, 1=pre-index, 2=post-index. }
function EncLdStPair(AIs64: Boolean; ALoad: Boolean; AMode: Integer;
  ARt, ARt2, ARn: Integer; AImm: Int64): Integer;
var
  Scale, W: Integer;
  Scaled: Int64;
begin
  if AIs64 then Scale := 3 else Scale := 2;
  if (AImm mod (Int64(1) shl Scale)) <> 0 then
    raise EArm64Assembler.Create('ldp/stp offset not multiple of reg size');
  Scaled := AImm div (Int64(1) shl Scale);
  if (Scaled < -64) or (Scaled > 63) then
    raise EArm64Assembler.Create('ldp/stp offset out of range');
  W := $28000000 or (Integer(Ord(AIs64)) shl 31);
  case AMode of
    0: W := W or (2 shl 23);   { signed offset }
    1: W := W or (3 shl 23);   { pre-index }
    2: W := W or (1 shl 23);   { post-index }
  end;
  if ALoad then W := W or (1 shl 22);
  Result := W or ((Integer(Scaled) and $7F) shl 15) or (ARt2 shl 10)
    or (ARn shl 5) or ARt;
end;

{ ---- the assembler driver ---------------------------------------------- }

procedure SplitLines(const AText: string; ALines: TList<string>);
var
  I, Start, Len, C: Integer;
begin
  Len := Length(AText);
  Start := 0;
  I := 0;
  while I < Len do
  begin
    C := StrAt(AText, I);
    if C = 10 then
    begin
      ALines.Add(Copy(AText, Start, I - Start));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  if Start < Len then
    ALines.Add(Copy(AText, Start, Len - Start));
end;

procedure TArm64Assembler.EmitW(AVal: Integer);
  begin
    FW.AppendDWord(FSection, AVal);
  end;

procedure TArm64Assembler.LineError(const AMsg: string);
  begin
    raise EArm64Assembler.Create('line ' + IntToStr(FL.LineNum) + ': '
      + AMsg + ' [' + TrimS(FL.RawLine) + ']');
  end;

{ Branch target: FUNCTION-INTERNAL label -> byte delta; anything else -> reloc
  (pass 2 only).

  A branch may be baked into the instruction ONLY when its target is a private
  label — control flow inside one routine.  A branch to an EXPORTED symbol needs
  a relocation even when the target sits in THIS SAME object and we already know
  the exact offset, because Apple's ld splits __text into atoms at symbol
  boundaries and relays them out; a hard-coded intra-object displacement then
  silently retargets to whatever now sits at that distance.

  That is not hypothetical.  Every 'bl _WriteAllToFd' in rtl.platform.posix was
  self-resolved to +0x4808, correct in the object; after ld's relayout the same
  word landed 0x11c past _WriteAllToFd, in the MIDDLE of _ArgvGet.  Twelve call
  sites, and every cc-linked binary — native and qbe — died on a garbage pointer
  before reaching main.  Our own linker keeps each input section atomic, so the
  baked offsets stayed valid there and the bug was invisible to every internally
  linked build, which is all the fixpoints and the whole self-hosting path. }
function TArm64Assembler.BranchDelta(const ASym: string;
  AKind: TContainerRelocKind; out AIsLocal: Boolean): Integer;
  var
    LSec, LOff: Integer;
    SymIdx: Integer;
  begin
    Result := 0;
    { FGlobals/FWeaks are filled in pass 1 and persist, so by pass 2 this test
      sees every export.  Pass 1 may misclassify a forward-declared export, but
      both arms emit one 4-byte word, so no offset can shift. }
    if FLabelSec.TryGetValue(ASym, LSec)
       and (not FGlobals.ContainsKey(ASym))
       and (not FWeaks.ContainsKey(ASym)) then
    begin
      AIsLocal := True;
      if TContainerSectionKind(LSec) <> FSection then
        LineError('cross-section branch to ' + ASym);
      FLabelOff.TryGetValue(ASym, LOff);
      Result := LOff - FCurOff;
      Exit;
    end;
    AIsLocal := False;
    if FPassNo = 2 then
    begin
      SymIdx := FW.FindSymbol(ASym);
      if SymIdx < 0 then
        SymIdx := FW.ExternSymbol(ASym);
      FW.AddReloc(FSection, FCurOff, SymIdx, AKind, 0);
    end;
  end;

  { Emit a symbol reloc for the current instruction word (pass 2). }
procedure TArm64Assembler.SymReloc(const ASym: string; ARef: TSymRef);
  var
    SymIdx: Integer;
  begin
    if FPassNo <> 2 then Exit;
    SymIdx := FW.FindSymbol(ASym);
    if SymIdx < 0 then
      SymIdx := FW.ExternSymbol(ASym);
    FW.AddReloc(FSection, FCurOff, SymIdx, SymRefToReloc(ARef), 0);
  end;

procedure TArm64Assembler.NeedOps(AN: Integer);
  begin
    if FNOps <> AN then
      LineError('expected ' + IntToStr(AN) + ' operands, got '
        + IntToStr(FNOps));
  end;

procedure TArm64Assembler.HandleDirective;
  var
    Vals: TList<string>;
    K: Integer;
    V: Int64;
    Sy: string;
    Ref: TSymRef;
    SymIdx: Integer;
    Txt: string;
    OctV: Integer;   { accumulated value of an octal .ascii escape }
    OctN: Integer;   { digits consumed so far (gas caps octal at three) }
  begin
    if FL.Mnemonic = '.text' then begin FSection := cskText; Exit; end;
    if FL.Mnemonic = '.data' then begin FSection := cskData; Exit; end;
    if FL.Mnemonic = '.section' then
    begin
      { Both spellings are accepted for every section: ELF's dotted names and
        Mach-O's (segment,section) pairs.  The backend emits whichever the TARGET
        assembler understands, and this assembler consumes either — so an
        --emit-asm dump stays assemblable by BOTH us and the platform tool.
        The __thread_* arms below are unreachable from these tests:
        '__thread_bss' contains neither '.bss' nor '__bss' (the underscore run
        before 'bss' is single), and likewise '__thread_data'. }
      if Pos('.rodata', FL.Args) >= 0 then FSection := cskRodata
      else if Pos('__const', FL.Args) >= 0 then FSection := cskRodata
      else if (Pos('.bss', FL.Args) >= 0) or
              (Pos('__bss', FL.Args) >= 0) then FSection := cskBss
      else if Pos('.tbss', FL.Args) >= 0 then FSection := cskTbss
      else if Pos('__thread_bss', FL.Args) >= 0 then FSection := cskTbss
      else if Pos('__thread_data', FL.Args) >= 0 then FSection := cskTdata
      else if Pos('__thread_vars', FL.Args) >= 0 then FSection := cskTvars
      else if Pos('.tdata', FL.Args) >= 0 then FSection := cskTdata
      else if Pos('.thread_vars', FL.Args) >= 0 then FSection := cskTvars
      else if Pos('.opdf', FL.Args) >= 0 then FSection := cskOpdf
      else if (Pos('.data', FL.Args) >= 0) or
              (Pos('__data', FL.Args) >= 0) then FSection := cskData
      else LineError('unsupported section: ' + FL.Args);
      Exit;
    end;
    if (FL.Mnemonic = '.globl') or (FL.Mnemonic = '.global') then
    begin
      if not FGlobals.ContainsKey(TrimS(FL.Args)) then
        FGlobals.Add(TrimS(FL.Args), True);
      Exit;
    end;
    { '.weak' is the ELF spelling, '.weak_definition' the Mach-O one (which the
      platform assembler requires ALONGSIDE .globl).  Accept both so an
      --emit-asm dump for either target assembles here. }
    if (FL.Mnemonic = '.weak') or (FL.Mnemonic = '.weak_definition') then
    begin
      if not FWeaks.ContainsKey(TrimS(FL.Args)) then
        FWeaks.Add(TrimS(FL.Args), True);
      Exit;
    end;
    if (FL.Mnemonic = '.balign') or (FL.Mnemonic = '.p2align') then
    begin
      V := ParseImmediate(TrimS(FL.Args));
      if FL.Mnemonic = '.p2align' then
        V := Int64(1) shl V;
      FW.AlignSection(FSection, Integer(V));
      Exit;
    end;
    if (FL.Mnemonic = '.byte') or (FL.Mnemonic = '.hword')
       or (FL.Mnemonic = '.word') or (FL.Mnemonic = '.quad') then
    begin
      Vals := TList<string>.Create();
      try
        SplitOperands(FL.Args, Vals);
        for K := 0 to Vals.Count - 1 do
        begin
          Sy := Vals.Get(K);
          if (FL.Mnemonic = '.quad') and
             (not ((StrAt(Sy, 0) >= Ord('0')) and (StrAt(Sy, 0) <= Ord('9')))
              and (StrAt(Sy, 0) <> Ord('-'))) then
          begin
            { .quad symbol -> 8-byte slot with an UNSIGNED reloc }
            if FPassNo = 2 then
            begin
              ParseSymRef(Sy, Sy, Ref);
              SymIdx := FW.FindSymbol(Sy);
              if SymIdx < 0 then SymIdx := FW.ExternSymbol(Sy);
              FW.AddReloc(FSection, FW.CurrentOffset(FSection), SymIdx,
                crkArm64Abs64, 0);
            end;
            FW.AppendQWord(FSection, 0);
            Continue;
          end;
          V := ParseImmediate(Sy);
          if FL.Mnemonic = '.byte' then FW.AppendByte(FSection, Integer(V))
          else if FL.Mnemonic = '.hword' then FW.AppendWord(FSection, Integer(V))
          else if FL.Mnemonic = '.word' then FW.AppendDWord(FSection, Integer(V))
          else FW.AppendQWord(FSection, V);
        end;
      finally
        Vals.Free();
      end;
      Exit;
    end;
    if FL.Mnemonic = '.double' then
    begin
      V := DoubleBits(_StrToDouble(PChar(TrimS(FL.Args))));
      FW.AppendQWord(FSection, V);
      Exit;
    end;
    if FL.Mnemonic = '.float' then
    begin
      FW.AppendDWord(FSection,
        SingleBits(Single(_StrToDouble(PChar(TrimS(FL.Args))))));
      Exit;
    end;
    if (FL.Mnemonic = '.ascii') or (FL.Mnemonic = '.asciz') then
    begin
      Txt := TrimS(FL.Args);
      if (Length(Txt) < 2) or (StrAt(Txt, 0) <> Ord('"')) then
        LineError('.ascii needs a quoted string');
      { C-unescape the quoted body }
      K := 1;
      while K < Length(Txt) - 1 do
      begin
        if (StrAt(Txt, K) = Ord('\')) and (K + 1 < Length(Txt) - 1) then
        begin
          K := K + 1;
          { Octal escape, up to three digits (gas caps it there).  Handled
            BEFORE the named escapes so a zero-padded '\000' consumes all
            three digits: a bare '\0' rule would take only the first and
            leave "00" to be copied through as literal characters, silently
            corrupting the data and desynchronising it from the length in
            the string header. }
          if (StrAt(Txt, K) >= Ord('0')) and (StrAt(Txt, K) <= Ord('7')) then
          begin
            OctV := StrAt(Txt, K) - Ord('0');
            OctN := 1;
            while (OctN < 3) and (K + 1 < Length(Txt) - 1)
                  and (StrAt(Txt, K + 1) >= Ord('0'))
                  and (StrAt(Txt, K + 1) <= Ord('7')) do
            begin
              K := K + 1;
              OctV := OctV * 8 + (StrAt(Txt, K) - Ord('0'));
              OctN := OctN + 1;
            end;
            FW.AppendByte(FSection, OctV and 255);
          end
          else
          case StrAt(Txt, K) of
            Ord('n'): FW.AppendByte(FSection, 10);
            Ord('t'): FW.AppendByte(FSection, 9);
            Ord('r'): FW.AppendByte(FSection, 13);
            Ord('\'): FW.AppendByte(FSection, Ord('\'));
            Ord('"'): FW.AppendByte(FSection, Ord('"'));
          else
            LineError('unsupported escape in .ascii');
          end;
        end
        else
          FW.AppendByte(FSection, StrAt(Txt, K));
        K := K + 1;
      end;
      if FL.Mnemonic = '.asciz' then
        FW.AppendByte(FSection, 0);
      Exit;
    end;
    if (FL.Mnemonic = '.zero') or (FL.Mnemonic = '.space') then
    begin
      V := ParseImmediate(TrimS(FL.Args));
      if (FSection = cskBss) or (FSection = cskTbss) then
        FW.ReserveBss(FSection, Integer(V))
      else
        FW.AppendZeros(FSection, Integer(V));
      Exit;
    end;
    if (FL.Mnemonic = '.file') or (FL.Mnemonic = '.size')
       or (FL.Mnemonic = '.ident') or (FL.Mnemonic = '.type')
       or (FL.Mnemonic = '.build_version') then
      Exit;   { no effect on the object }
    LineError('unknown directive: ' + FL.Mnemonic);
  end;

procedure TArm64Assembler.EncodeInstr;
  var
    Delta: Integer;
    IsLocal: Boolean;
    Sz, Opc: Integer;
    Wd: Integer;
    ShiftAmt: Integer;
    WidthM1: Integer;
  begin
    { zero-operand }
    if FL.Mnemonic = 'nop' then begin EmitW(Integer($D503201F)); Exit; end;
    if FL.Mnemonic = 'ret' then begin EmitW(Integer($D65F03C0)); Exit; end;

    if FL.Mnemonic = 'brk' then
    begin
      NeedOps(1);
      EmitW(Integer($D4200000) or (Integer(FA[0].Imm and $FFFF) shl 5));
      Exit;
    end;
    if FL.Mnemonic = 'svc' then
    begin
      NeedOps(1);
      EmitW(Integer($D4000001) or (Integer(FA[0].Imm and $FFFF) shl 5));
      Exit;
    end;

    if (FL.Mnemonic = 'br') or (FL.Mnemonic = 'blr') then
    begin
      NeedOps(1);
      if FL.Mnemonic = 'br' then
        EmitW(Integer($D61F0000) or (FA[0].Reg shl 5))
      else
        EmitW(Integer($D63F0000) or (FA[0].Reg shl 5));
      Exit;
    end;

    if (FL.Mnemonic = 'b') or (FL.Mnemonic = 'bl') then
    begin
      NeedOps(1);
      Delta := BranchDelta(FA[0].Sym, crkArm64Branch26, IsLocal);
      Wd := Integer($14000000);
      if FL.Mnemonic = 'bl' then Wd := Integer($94000000);
      if IsLocal then
        Wd := Wd or ((Delta div 4) and $3FFFFFF);
      EmitW(Wd);
      Exit;
    end;

    if FL.Mnemonic = 'b.cond' then
    begin
      NeedOps(1);
      Delta := BranchDelta(FA[0].Sym, crkNone, IsLocal);
      { pass 1 may see a FORWARD label that is not collected yet — emit a
        placeholder; pass 2 has the full label table and errors for real }
      if (not IsLocal) and (FPassNo = 2) then
        LineError('b.<cond> target must be a local label');
      EmitW(Integer($54000000) or (((Delta div 4) and $7FFFF) shl 5)
        or CondCode(FL.Cond));
      Exit;
    end;

    if (FL.Mnemonic = 'cbz') or (FL.Mnemonic = 'cbnz') then
    begin
      NeedOps(2);
      Delta := BranchDelta(FA[1].Sym, crkNone, IsLocal);
      if (not IsLocal) and (FPassNo = 2) then
        LineError('cbz/cbnz target must be a local label');
      Wd := Integer($34000000) or (SfBit(FA[0].Is64) shl 31);
      if FL.Mnemonic = 'cbnz' then Wd := Wd or $01000000;
      EmitW(Wd or (((Delta div 4) and $7FFFF) shl 5) or FA[0].Reg);
      Exit;
    end;

    if (FL.Mnemonic = 'tbz') or (FL.Mnemonic = 'tbnz') then
    begin
      NeedOps(3);
      Delta := BranchDelta(FA[2].Sym, crkNone, IsLocal);
      if (not IsLocal) and (FPassNo = 2) then
        LineError('tbz/tbnz target must be a local label');
      Wd := Integer($36000000);
      if FL.Mnemonic = 'tbnz' then Wd := Wd or $01000000;
      Wd := Wd or ((Integer(FA[1].Imm) and $20) shl 26)   { b5 -> bit 31 }
        or ((Integer(FA[1].Imm) and $1F) shl 19)
        or (((Delta div 4) and $3FFF) shl 5) or FA[0].Reg;
      EmitW(Wd);
      Exit;
    end;

    if FL.Mnemonic = 'adrp' then
    begin
      NeedOps(2);
      if FA[1].SymRef <> srPage then
        if not (FA[1].SymRef in [srGotPage, srTlvPage]) then
          LineError('adrp needs @PAGE/@GOTPAGE/@TLVPPAGE operand');
      SymReloc(FA[1].Sym, FA[1].SymRef);
      EmitW(Integer($90000000) or FA[0].Reg);
      Exit;
    end;

    if (FL.Mnemonic = 'movz') or (FL.Mnemonic = 'movk')
       or (FL.Mnemonic = 'movn') then
    begin
      ShiftAmt := 0;
      if FNOps = 3 then
      begin
        { third operand is 'lsl #N' — extract the amount after '#' }
        Wd := Pos('#', FA[2].Sym);
        if Wd < 0 then
          LineError('movz/movk shift operand must be lsl #N');
        ShiftAmt := Integer(ParseImmediate(
          TrimS(Copy(FA[2].Sym, Wd, Length(FA[2].Sym) - Wd))));
      end
      else
        NeedOps(2);
      if FL.Mnemonic = 'movz' then Opc := 2
      else if FL.Mnemonic = 'movk' then Opc := 3
      else Opc := 0;
      EmitW(EncMovWide(FA[0].Is64, Opc, FA[0].Reg, FA[1].Imm, ShiftAmt));
      Exit;
    end;

    if FL.Mnemonic = 'mov' then
    begin
      NeedOps(2);
      if FA[1].Kind = okImm then
      begin
        if (FA[1].Imm >= 0) and (FA[1].Imm <= $FFFF) then
          EmitW(EncMovWide(FA[0].Is64, 2, FA[0].Reg, FA[1].Imm, 0))
        else if (FA[1].Imm < 0) and (FA[1].Imm >= -$10000) then
          EmitW(EncMovWide(FA[0].Is64, 0, FA[0].Reg, (not FA[1].Imm) and $FFFF, 0))
        else
          LineError('mov immediate out of range (use movz/movk pairs)');
        Exit;
      end;
      if FA[0].IsSP or FA[1].IsSP then
      begin
        { mov sp involves add #0 }
        EmitW(EncAddSubImm(True, False, False, FA[0].Reg, FA[1].Reg, 0));
        Exit;
      end;
      { orr rd, xzr, rm }
      EmitW(EncLogicReg(FA[0].Is64, 1, FA[0].Reg, 31, FA[1].Reg));
      Exit;
    end;

    if (FL.Mnemonic = 'add') or (FL.Mnemonic = 'sub')
       or (FL.Mnemonic = 'adds') or (FL.Mnemonic = 'subs') then
    begin
      NeedOps(3);
      if (FA[2].Kind = okSym) and (FA[2].SymRef in
         [srPageOff, srGotPageOff, srTlvPageOff]) then
      begin
        { add xN, xM, sym@PAGEOFF }
        SymReloc(FA[2].Sym, FA[2].SymRef);
        EmitW(EncAddSubImm(FA[0].Is64, False, False, FA[0].Reg, FA[1].Reg, 0));
        Exit;
      end;
      if FA[2].Kind = okImm then
        EmitW(EncAddSubImm(FA[0].Is64, StrAt(FL.Mnemonic, 0) = Ord('s'),
          Length(FL.Mnemonic) = 4, FA[0].Reg, FA[1].Reg, FA[2].Imm))
      else if FA[0].IsSP or FA[1].IsSP then
        { sp with a register operand: ONLY the extended-register form treats
          register 31 as sp — the shifted form would make it xzr and the
          instruction a no-op.  Same IsSP rule the `mov` case above applies. }
        EmitW(EncAddSubExtReg(FA[0].Is64, StrAt(FL.Mnemonic, 0) = Ord('s'),
          Length(FL.Mnemonic) = 4, FA[0].Reg, FA[1].Reg, FA[2].Reg))
      else
        EmitW(EncAddSubReg(FA[0].Is64, StrAt(FL.Mnemonic, 0) = Ord('s'),
          Length(FL.Mnemonic) = 4, FA[0].Reg, FA[1].Reg, FA[2].Reg));
      Exit;
    end;

    if FL.Mnemonic = 'cmp' then
    begin
      NeedOps(2);
      if FA[1].Kind = okImm then
        EmitW(EncAddSubImm(FA[0].Is64, True, True, 31, FA[0].Reg, FA[1].Imm))
      else
        EmitW(EncAddSubReg(FA[0].Is64, True, True, 31, FA[0].Reg, FA[1].Reg));
      Exit;
    end;

    if FL.Mnemonic = 'neg' then
    begin
      NeedOps(2);
      EmitW(EncAddSubReg(FA[0].Is64, True, False, FA[0].Reg, 31, FA[1].Reg));
      Exit;
    end;

    if (FL.Mnemonic = 'and') or (FL.Mnemonic = 'orr')
       or (FL.Mnemonic = 'eor') or (FL.Mnemonic = 'ands') then
    begin
      NeedOps(3);
      if FL.Mnemonic = 'and' then Opc := 0
      else if FL.Mnemonic = 'orr' then Opc := 1
      else if FL.Mnemonic = 'eor' then Opc := 2
      else Opc := 3;
      if FA[2].Kind <> okReg then
        LineError('logical immediates not supported — materialise first');
      EmitW(EncLogicReg(FA[0].Is64, Opc, FA[0].Reg, FA[1].Reg, FA[2].Reg));
      Exit;
    end;

    if FL.Mnemonic = 'mvn' then
    begin
      NeedOps(2);
      { orn rd, xzr, rm }
      EmitW(EncLogicReg(FA[0].Is64, 1, FA[0].Reg, 31, FA[1].Reg)
        or (1 shl 21));
      Exit;
    end;

    if FL.Mnemonic = 'mul' then
    begin
      NeedOps(3);
      EmitW(EncMulAdd(FA[0].Is64, False, FA[0].Reg, FA[1].Reg, FA[2].Reg, 31));
      Exit;
    end;
    if (FL.Mnemonic = 'madd') or (FL.Mnemonic = 'msub') then
    begin
      NeedOps(4);
      EmitW(EncMulAdd(FA[0].Is64, FL.Mnemonic = 'msub',
        FA[0].Reg, FA[1].Reg, FA[2].Reg, FA[3].Reg));
      Exit;
    end;
    if (FL.Mnemonic = 'sdiv') or (FL.Mnemonic = 'udiv') then
    begin
      NeedOps(3);
      EmitW(EncDiv(FA[0].Is64, FL.Mnemonic = 'sdiv',
        FA[0].Reg, FA[1].Reg, FA[2].Reg));
      Exit;
    end;

    if (FL.Mnemonic = 'lsl') or (FL.Mnemonic = 'lsr') or (FL.Mnemonic = 'asr') then
    begin
      NeedOps(3);
      if FA[0].Is64 then WidthM1 := 63 else WidthM1 := 31;
      if FA[2].Kind = okReg then
      begin
        if FL.Mnemonic = 'lsl' then Opc := 8
        else if FL.Mnemonic = 'lsr' then Opc := 9
        else Opc := 10;
        EmitW(EncShiftVar(FA[0].Is64, Opc, FA[0].Reg, FA[1].Reg, FA[2].Reg));
        Exit;
      end;
      ShiftAmt := Integer(FA[2].Imm);
      if FL.Mnemonic = 'lsl' then
        EmitW(EncBitfield(FA[0].Is64, False, FA[0].Reg, FA[1].Reg,
          (WidthM1 + 1 - ShiftAmt) and WidthM1, WidthM1 - ShiftAmt))
      else if FL.Mnemonic = 'lsr' then
        EmitW(EncBitfield(FA[0].Is64, False, FA[0].Reg, FA[1].Reg,
          ShiftAmt, WidthM1))
      else
        EmitW(EncBitfield(FA[0].Is64, True, FA[0].Reg, FA[1].Reg,
          ShiftAmt, WidthM1));
      Exit;
    end;

    if FL.Mnemonic = 'sxtw' then
    begin
      NeedOps(2);
      EmitW(Integer($93407C00) or (FA[1].Reg shl 5) or FA[0].Reg);
      Exit;
    end;

    if FL.Mnemonic = 'cset' then
    begin
      NeedOps(2);
      { csinc rd, zr, zr, inv(cond) }
      EmitW((SfBit(FA[0].Is64) shl 31) or $1A800400 or (31 shl 16)
        or (CondInvert(CondCode(LowerS(TrimS(FA[1].Sym)))) shl 12)
        or (31 shl 5) or FA[0].Reg);
      Exit;
    end;

    { loads/stores }
    if (FL.Mnemonic = 'ldr') or (FL.Mnemonic = 'str')
       or (FL.Mnemonic = 'ldrb') or (FL.Mnemonic = 'strb')
       or (FL.Mnemonic = 'ldrh') or (FL.Mnemonic = 'strh')
       or (FL.Mnemonic = 'ldrsw')
       or (FL.Mnemonic = 'ldur') or (FL.Mnemonic = 'stur') then
    begin
      { post-index '[sp], #16' splits at the top-level comma into a third
        immediate operand — fold it back (same shape as ldp/stp). }
      if (FNOps = 3) and (FA[1].Kind = okMem) and (FA[2].Kind = okImm) then
      begin
        FA[1].PostIdx := True;
        FA[1].MemImm := FA[2].Imm;
        FNOps := 2;
      end;
      NeedOps(2);
      if FA[1].Kind <> okMem then
        LineError('memory operand expected');
      { pre/post-index single-register forms ([sp, #-16]! / [sp], #16) —
        the backend's 16-byte stack brackets. }
      if FA[1].PreIdx or FA[1].PostIdx then
      begin
        if FA[0].Is64 then Sz := 3 else Sz := 2;
        if StrAt(FL.Mnemonic, 0) = Ord('l') then Opc := 1 else Opc := 0;
        EmitW(EncodeLdStPrePost(Sz, FA[0].IsFP, Opc, FA[1].PreIdx,
          FA[0].Reg, FA[1].Base, FA[1].MemImm));
        Exit;
      end;
      { size/opc per variant }
      if FA[0].IsFP then
      begin
        if FA[0].Is64 then Sz := 3 else Sz := 2;
        if StrAt(FL.Mnemonic, 0) = Ord('l') then Opc := 1 else Opc := 0;
        if FA[1].MemSymRef <> srNone then
        begin
          SymReloc(FA[1].MemSym, FA[1].MemSymRef);
          EmitW(EncLdStUImm(Sz, True, Opc, FA[0].Reg, FA[1].Base, 0));
        end
        else
          EmitW(EncLdStUImm(Sz, True, Opc, FA[0].Reg, FA[1].Base, FA[1].MemImm));
        Exit;
      end;
      if FL.Mnemonic = 'ldrsw' then begin Sz := 2; Opc := 2; end
      else if (FL.Mnemonic = 'ldrb') or (FL.Mnemonic = 'strb') then
      begin
        Sz := 0;
        if StrAt(FL.Mnemonic, 0) = Ord('l') then Opc := 1 else Opc := 0;
      end
      else if (FL.Mnemonic = 'ldrh') or (FL.Mnemonic = 'strh') then
      begin
        Sz := 1;
        if StrAt(FL.Mnemonic, 0) = Ord('l') then Opc := 1 else Opc := 0;
      end
      else
      begin
        if FA[0].Is64 then Sz := 3 else Sz := 2;
        if StrAt(FL.Mnemonic, 0) = Ord('l') then Opc := 1 else Opc := 0;
      end;
      if (FL.Mnemonic = 'ldur') or (FL.Mnemonic = 'stur') then
      begin
        EmitW(EncLdStUnscaled(Sz, False, Opc, FA[0].Reg, FA[1].Base,
          FA[1].MemImm));
        Exit;
      end;
      if FA[1].MemSymRef <> srNone then
      begin
        SymReloc(FA[1].MemSym, FA[1].MemSymRef);
        EmitW(EncLdStUImm(Sz, False, Opc, FA[0].Reg, FA[1].Base, 0));
        Exit;
      end;
      { A plain ldr/str with an offset that is negative or not a multiple of the
        access size cannot use the scaled 12-bit form, but IS a valid unscaled
        ldur/stur when it fits the signed 9-bit range [-256..255].  GNU `as`
        auto-selects ldur/stur in exactly this case; do the same so a codegen
        site that emits e.g. `ldr x0, [x1, #20]` (20 not a multiple of 8)
        assembles instead of raising. }
      if ((FA[1].MemImm < 0) or
          ((FA[1].MemImm mod (Int64(1) shl Sz)) <> 0)) and
         (FA[1].MemImm >= -256) and (FA[1].MemImm <= 255) then
      begin
        EmitW(EncLdStUnscaled(Sz, False, Opc, FA[0].Reg, FA[1].Base,
          FA[1].MemImm));
        Exit;
      end;
      EmitW(EncLdStUImm(Sz, False, Opc, FA[0].Reg, FA[1].Base, FA[1].MemImm));
      Exit;
    end;

    { LSE atomics (acquire+release variants) — runtime.atomic.arm64.
      LDADDAL Rs, Rt, [Xn]: Rt := [Xn]; [Xn] += Rs (atomic fetch-add).
      SWPAL   Rs, Rt, [Xn]: Rt := [Xn]; [Xn] := Rs (atomic exchange).
      CASAL   Rs, Rt, [Xn]: if [Xn] = Rs then [Xn] := Rt; Rs := old. }
    if (FL.Mnemonic = 'ldaddal') or (FL.Mnemonic = 'swpal')
       or (FL.Mnemonic = 'casal') then
    begin
      NeedOps(3);
      if FA[2].Kind <> okMem then
        LineError('memory operand expected');
      if FA[2].MemImm <> 0 then
        LineError('LSE atomics take a plain [Xn] operand');
      if FL.Mnemonic = 'casal' then
      begin
        if FA[0].Is64 then Wd := Integer($C8E0FC00)
        else Wd := Integer($88E0FC00);
      end
      else
      begin
        if FA[0].Is64 then Wd := Integer($F8E00000)
        else Wd := Integer($B8E00000);
        if FL.Mnemonic = 'swpal' then Wd := Wd or $8000;
      end;
      EmitW(Wd or (FA[0].Reg shl 16) or (FA[2].Base shl 5) or FA[1].Reg);
      Exit;
    end;

    if (FL.Mnemonic = 'ldp') or (FL.Mnemonic = 'stp') then
    begin
      { post-index '[sp], #16' splits at the top-level comma into a 4th
        immediate operand — fold it back into the memory operand }
      if (FNOps = 4) and (FA[2].Kind = okMem) and (FA[3].Kind = okImm) then
      begin
        FA[2].PostIdx := True;
        FA[2].MemImm := FA[3].Imm;
        FNOps := 3;
      end;
      NeedOps(3);
      if FA[2].Kind <> okMem then
        LineError('memory operand expected');
      Opc := 0;   { signed-offset mode }
      if FA[2].PreIdx then Opc := 1
      else if FA[2].PostIdx then Opc := 2;
      EmitW(EncLdStPair(FA[0].Is64, FL.Mnemonic = 'ldp', Opc,
        FA[0].Reg, FA[1].Reg, FA[2].Base, FA[2].MemImm));
      Exit;
    end;

    { floating point }
    if (FL.Mnemonic = 'fadd') or (FL.Mnemonic = 'fsub')
       or (FL.Mnemonic = 'fmul') or (FL.Mnemonic = 'fdiv') then
    begin
      NeedOps(3);
      if FL.Mnemonic = 'fadd' then Opc := $2
      else if FL.Mnemonic = 'fsub' then Opc := $3
      else if FL.Mnemonic = 'fmul' then Opc := $0
      else Opc := $1;
      Wd := Integer($1E200800) or (Opc shl 12)
        or (FA[2].Reg shl 16) or (FA[1].Reg shl 5) or FA[0].Reg;
      if FA[0].Is64 then Wd := Wd or (1 shl 22);
      EmitW(Wd);
      Exit;
    end;
    if FL.Mnemonic = 'fcmp' then
    begin
      NeedOps(2);
      Wd := Integer($1E202000) or (FA[0].Reg shl 5);
      if FA[0].Is64 then Wd := Wd or (1 shl 22);
      if FA[1].Kind = okFImm then
        Wd := Wd or 8
      else
        Wd := Wd or (FA[1].Reg shl 16);
      EmitW(Wd);
      Exit;
    end;
    if FL.Mnemonic = 'scvtf' then
    begin
      NeedOps(2);
      { int -> fp: scvtf dD, xN }
      Wd := Integer($1E220000) or (FA[1].Reg shl 5) or FA[0].Reg;
      if FA[0].Is64 then Wd := Wd or (1 shl 22);       { double dest }
      if FA[1].Is64 then Wd := Wd or (1 shl 31);       { 64-bit source }
      EmitW(Wd);
      Exit;
    end;
    if FL.Mnemonic = 'fcvt' then
    begin
      { precision conversion between scalar fp registers:
          fcvt dD, sN  (single -> double) = $1E22C000 | Rn<<5 | Rd
          fcvt sD, dN  (double -> single) = $1E624000 | Rn<<5 | Rd }
      NeedOps(2);
      if not (FA[0].IsFP and FA[1].IsFP) then
        LineError('fcvt needs two fp registers');
      if FA[0].Is64 = FA[1].Is64 then
        LineError('fcvt needs one single and one double register');
      if FA[0].Is64 then
        Wd := Integer($1E22C000) or (FA[1].Reg shl 5) or FA[0].Reg
      else
        Wd := Integer($1E624000) or (FA[1].Reg shl 5) or FA[0].Reg;
      EmitW(Wd);
      Exit;
    end;
    if FL.Mnemonic = 'fcvtzs' then
    begin
      NeedOps(2);
      Wd := Integer($1E380000) or (FA[1].Reg shl 5) or FA[0].Reg;
      if FA[1].Is64 then Wd := Wd or (1 shl 22);       { double source }
      if FA[0].Is64 then Wd := Wd or (1 shl 31);       { 64-bit dest }
      EmitW(Wd);
      Exit;
    end;
    if FL.Mnemonic = 'fmov' then
    begin
      NeedOps(2);
      if FA[0].IsFP and FA[1].IsFP then
      begin
        Wd := Integer($1E204000) or (FA[1].Reg shl 5) or FA[0].Reg;
        if FA[0].Is64 then Wd := Wd or (1 shl 22);
        EmitW(Wd);
        Exit;
      end;
      if FA[0].IsFP then
        { fmov dN, xM }
        EmitW(Integer($9E670000) or (FA[1].Reg shl 5) or FA[0].Reg)
      else
        { fmov xN, dM }
        EmitW(Integer($9E660000) or (FA[1].Reg shl 5) or FA[0].Reg);
      Exit;
    end;

    LineError('unknown instruction: ' + FL.Mnemonic);
  end;

function TArm64Assembler.Assemble(const AAsmText: string): string;
var
  Lines: TList<string>;
  Parsed: array of TA64Line;
  I, J, PassIdx, LSec, LOff: Integer;
  Ops: TList<string>;
  Bind: TContainerSymBind;

begin
  Lines := TList<string>.Create();
  FLabelSec := TDictionary<string, Integer>.Create();
  FLabelOff := TDictionary<string, Integer>.Create();
  FGlobals := TDictionary<string, Boolean>.Create();
  FWeaks := TDictionary<string, Boolean>.Create();
  FW := TMachOObjectWriter.Create();
  try
    SplitLines(AAsmText, Lines);
    SetLength(Parsed, Lines.Count);
    for I := 0 to Lines.Count - 1 do
      Parsed[I] := ParseLine(Lines.Get(I), I + 1);

    for PassIdx := 1 to 2 do
    begin
      FPassNo := PassIdx;
      if FPassNo = 2 then
      begin
        FW.Free();
        FW := TMachOObjectWriter.Create();   { fresh writer for pass 2 }
        { Define every label symbol BEFORE encoding pass 2, so relocations
          against local data labels (adrp/@PAGEOFF targets) bind to the
          DEFINED symbol instead of minting an undefined extern. }
        for I := 0 to Length(Parsed) - 1 do
        begin
          FL := Parsed[I];
          if FL.Kind <> alLabel then Continue;
          if not FLabelSec.TryGetValue(FL.Mnemonic, LSec) then Continue;
          FLabelOff.TryGetValue(FL.Mnemonic, LOff);
          { WEAK WINS over global, and the order is load-bearing on Mach-O.
            ELF marks a weak definition with '.weak' ALONE, so a symbol landed
            in exactly one set and the precedence never mattered.  Mach-O needs
            BOTH '.globl' and '.weak_definition' for the same symbol, so with
            global checked first every weak RTL definition would have been
            emitted STRONG — silently destroying the weak-collapse the
            whole-program-per-unit build depends on (two objects defining the
            same RTL symbol would become a duplicate-symbol error). }
          if FWeaks.ContainsKey(FL.Mnemonic) then Bind := csbWeak
          else if FGlobals.ContainsKey(FL.Mnemonic) then Bind := csbGlobal
          else Bind := csbLocal;
          FW.DefineSymbol(FL.Mnemonic, TContainerSectionKind(LSec), LOff,
            0, Bind, cstNone);
        end;
      end;
      FSection := cskText;
      for I := 0 to Length(Parsed) - 1 do
      begin
        FL := Parsed[I];
        case FL.Kind of
          alBlank: ;
          alLabel:
          begin
            if FPassNo = 1 then
            begin
              if FLabelSec.ContainsKey(FL.Mnemonic) then
                LineError('duplicate label: ' + FL.Mnemonic);
              FLabelSec.Add(FL.Mnemonic, Ord(FSection));
              FLabelOff.Add(FL.Mnemonic, FW.CurrentOffset(FSection));
            end;
          end;
          alDirective:
            Self.HandleDirective();
          alInstr:
          begin
            FCurOff := FW.CurrentOffset(FSection);
            Ops := TList<string>.Create();
            try
              SplitOperands(FL.Args, Ops);
              FNOps := Ops.Count;
              SetLength(FA, FNOps);
              for J := 0 to FNOps - 1 do
              begin
                FA[J] := ParseOperand(Ops.Get(J));
                { branch/cset targets parse as okSym; keep raw for cset }
                if (FA[J].Kind = okSym) and (FA[J].Sym = '') then
                  FA[J].Sym := Ops.Get(J);
              end;
              { cset's condition operand: store raw name in Sym }
              if (FL.Mnemonic = 'cset') and (FNOps = 2) then
                FA[1].Sym := Ops.Get(1);
              Self.EncodeInstr();
            finally
              Ops.Free();
            end;
          end;
        end;
      end;
    end;

    { the .bif payload is data, not assembled text, so it is appended straight
      into its own section just before the object is serialised }
    if IfacePayload <> '' then
      FW.Append(cskIface, IfacePayload);

    Result := FW.Finish();
  finally
    SetLength(Parsed, 0);
    SetLength(FA, 0);
    FWeaks.Free();
    FGlobals.Free();
    FLabelSec.Free();
    FLabelOff.Free();
    Lines.Free();
    FW.Free();
  end;
end;

function AssembleArm64ToBytes(const AAsmText: string): string;
var
  Asmblr: TArm64Assembler;
begin
  Asmblr := TArm64Assembler.Create();
  try
    Result := Asmblr.Assemble(AAsmText);
  finally
    Asmblr.Free();
  end;
end;

procedure AssembleArm64ToObject(const AAsmText: string;
  const AOutputPath: string; const AIfaceBytes: string);
var
  Buf: string;
  FOut: TFileOutputStream;
  Asmblr: TArm64Assembler;
begin
  Asmblr := TArm64Assembler.Create();
  try
    { the .bif payload rides into the object as a (__BLAISE,__blaise_iface)
      section — see TArm64Assembler.IfacePayload }
    Asmblr.IfacePayload := AIfaceBytes;
    Buf := Asmblr.Assemble(AAsmText);
  finally
    Asmblr.Free();
  end;
  FOut := TFileOutputStream.Create(AOutputPath);
  try
    FOut.Write(PChar(Buf), Length(Buf));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

end.
