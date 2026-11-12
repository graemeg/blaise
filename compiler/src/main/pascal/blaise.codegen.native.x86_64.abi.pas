{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.x86_64.abi;

{ Per-target strategy objects for the x86-64 backend.

  The x86-64 backend has no OS branch.  Where two x86-64 targets need
  different machine code, the backend asks a strategy object that the target
  toolkit supplies (docs/windows-x86_64-backend-design.adoc, "Governing rule"):

  * TX86BoundaryAbi -- the calling convention at the foreign-code boundary.
  * TX86TlsModel    -- how a threadvar is addressed.

  The System V / ELF adapters reproduce the code the backend emitted before
  the seam existed, character for character. }

interface

uses
  SysUtils;

type
  { Emits one line of assembly through the backend, so the backend's stream
    observers (stack-depth tracking, register-promotion rewrites) see it. }
  TX86EmitProc = procedure(const ALine: string) of object;

  { How the backend classifies one argument of a foreign call: an integer or
    pointer (a var parameter is its address), a Single, a Double, or a record
    passed by value (with its size). }
  TX86ForeignArgKind = (fakInt, fakSingle, fakDouble, fakRecord);

  { Where one argument of a foreign call travels. }
  TX86ForeignArgLoc = record
    { The register, or '' when the argument goes on the stack. }
    Reg: string;
    { A second register that also receives the value (a variadic float), or
      ''. }
    MirrorReg: string;
    { The argument's offset from %rsp at the call, when Reg is ''. }
    StackOff: Int;
    { A record that travels as the address of a copy the caller makes. }
    ByRef: Boolean;
  end;

  { The calling convention where control crosses into or out of foreign
    code (design decision D1: the internal convention is System V on every
    target).  The backend evaluates a foreign call's arguments; the strategy
    says where each one goes.  The foreign-entry lowering (a routine foreign
    code calls) is added in M5. }
  TX86BoundaryAbi = class
  public
    { True when frames of a page or more must be probed in the prologue. }
    function NeedsStackProbe: Boolean; virtual; abstract;
    { True when a C-convention routine differs from the internal one.  The
      foreign-call queries below are asked only when it does. }
    function ForeignDiffers: Boolean; virtual; abstract;
    { The bytes a caller reserves at the bottom of its outgoing area for a
      foreign call with AArgCount arguments: the callee's home space plus
      the stack-passed arguments. }
    function ForeignOutgoingBytes(AArgCount: Int): Int; virtual; abstract;
    { Where argument AIndex (0-based, counting every argument the callee
      sees) of kind AKind and, for a record, ASize bytes travels.  AVariadic
      marks an argument in the variadic part of the call. }
    function ForeignArgLoc(AIndex: Int; AKind: TX86ForeignArgKind;
      ASize: Int; AVariadic: Boolean): TX86ForeignArgLoc; virtual; abstract;
    { True when a foreign routine returns a record of ASize bytes in RAX;
      False when the caller passes the address of the result as a hidden
      argument 0, ahead of the declared ones. }
    function ForeignRecordResultInRax(ASize: Int): Boolean; virtual; abstract;
  end;

  { System V AMD64: the C convention IS the internal convention, and the
    stack grows on demand, so neither probing nor translation is needed. }
  TSysVBoundaryAbi = class(TX86BoundaryAbi)
  public
    function NeedsStackProbe: Boolean; override;
    function ForeignDiffers: Boolean; override;
    { Never asked: a System V foreign call is an internal call. }
    function ForeignOutgoingBytes(AArgCount: Int): Int; override;
    function ForeignArgLoc(AIndex: Int; AKind: TX86ForeignArgKind;
      ASize: Int; AVariadic: Boolean): TX86ForeignArgLoc; override;
    function ForeignRecordResultInRax(ASize: Int): Boolean; override;
  end;

  { The Microsoft x64 convention (windows-x86_64-backend-design.adoc,
    "Outbound calls"): arguments are positional, the first four in RCX, RDX,
    R8, R9 or XMM0-XMM3 by type, the rest in 8-byte stack slots above 32
    bytes of home space; a record of 1, 2, 4 or 8 bytes travels as its bytes,
    any other as the address of a copy; a variadic float in the first four
    is also copied to the matching integer register.  A record result of 1,
    2, 4 or 8 bytes comes back in RAX; any other is written through a hidden
    pointer argument in RCX, the callee returning it in RAX.  Windows grows a
    thread's stack one guard page at a time, so large frames are probed. }
  TWin64BoundaryAbi = class(TX86BoundaryAbi)
  public
    function NeedsStackProbe: Boolean; override;
    function ForeignDiffers: Boolean; override;
    function ForeignOutgoingBytes(AArgCount: Int): Int; override;
    function ForeignArgLoc(AIndex: Int; AKind: TX86ForeignArgKind;
      ASize: Int; AVariadic: Boolean): TX86ForeignArgLoc; override;
    function ForeignRecordResultInRax(ASize: Int): Boolean; override;
  end;

  { Threadvar addressing.  ASym is the final assembler symbol of the TLS slot
    (owner-prefixed, with any _obj / _itab suffix already applied). }
  TX86TlsModel = class
  public
    { A memory operand addressing ASym that needs no preparatory code and no
      register, so a caller may splice it into any instruction. }
    function DirectOperand(const ASym: string): string; virtual; abstract;
    { Emit code leaving the ADDRESS of ASym in ADstReg, clobbering nothing
      else. }
    procedure EmitAddress(const ASym, ADstReg: string;
      AEmit: TX86EmitProc); virtual; abstract;
    { The backend's line hook, applied to every emitted line before it is
      written.  Returns True after emitting a replacement for ALine through
      AEmit; False when ALine needs nothing and was not emitted. }
    function RewriteLine(const ALine: string;
      AEmit: TX86EmitProc): Boolean; virtual; abstract;
  end;

  { ELF local-exec: %fs holds the thread pointer; a threadvar is at a
    negative link-time offset from it (R_X86_64_TPOFF32). }
  TElfLocalExecTls = class(TX86TlsModel)
  public
    function DirectOperand(const ASym: string): string; override;
    procedure EmitAddress(const ASym, ADstReg: string;
      AEmit: TX86EmitProc); override;
    { `leaq <operand>, %reg` yields the bare offset (lea ignores the
      segment), so it becomes thread pointer plus offset. }
    function RewriteLine(const ALine: string;
      AEmit: TX86EmitProc): Boolean; override;
  end;

  { PE TLS (windows-x86_64-backend-design.adoc, "Thread-local storage"): the
    loader gives each thread a copy of the image's TLS template and stores
    its address in the TEB's ThreadLocalStoragePointer array (%gs:88), at the
    image's index.  An executable's index is 0; runtime.start.windows checks
    that _tls_index is.  A variable is at a positive offset into the block
    (sym@tpoff, resolved by the PE linker).

    Reaching the block takes a register, and the backend splices operands
    into arbitrary instructions and reuses them across calls.  So
    DirectOperand returns a marker, and RewriteLine expands every line that
    contains one: it loads the block into %r11, then emits the line with
    sym@tpoff(%r11) in place of the marker.  Each use reloads the base, so a
    call in between cannot leave it stale.  %r11 is caller-saved scratch the
    backend never keeps live across a global variable's operand; a line that
    uses %r11 itself as well as the marker -- other than as the destination
    of a load or address of the operand -- is reported, never miscompiled. }
  TPeTlsModel = class(TX86TlsModel)
  public
    function DirectOperand(const ASym: string): string; override;
    procedure EmitAddress(const ASym, ADstReg: string;
      AEmit: TX86EmitProc); override;
    function RewriteLine(const ALine: string;
      AEmit: TX86EmitProc): Boolean; override;
  end;

implementation

{ TSysVBoundaryAbi }

function TSysVBoundaryAbi.NeedsStackProbe: Boolean;
begin
  Result := False;
end;

function TSysVBoundaryAbi.ForeignDiffers: Boolean;
begin
  Result := False;
end;

function TSysVBoundaryAbi.ForeignOutgoingBytes(AArgCount: Int): Int;
begin
  raise Exception.Create('internal: a System V foreign call is an ' +
    'internal call');
end;

function TSysVBoundaryAbi.ForeignArgLoc(AIndex: Int;
  AKind: TX86ForeignArgKind; ASize: Int;
  AVariadic: Boolean): TX86ForeignArgLoc;
begin
  raise Exception.Create('internal: a System V foreign call is an ' +
    'internal call');
end;

function TSysVBoundaryAbi.ForeignRecordResultInRax(ASize: Int): Boolean;
begin
  raise Exception.Create('internal: a System V foreign call is an ' +
    'internal call');
end;

{ TWin64BoundaryAbi }

const
  Win64IntArgRegs: array[0..3] of string = ('%rcx', '%rdx', '%r8', '%r9');
  Win64XmmArgRegs: array[0..3] of string = ('%xmm0', '%xmm1', '%xmm2', '%xmm3');
  { The callee's home space for the four register arguments. }
  Win64HomeBytes = 32;

function TWin64BoundaryAbi.NeedsStackProbe: Boolean;
begin
  Result := True;
end;

function TWin64BoundaryAbi.ForeignDiffers: Boolean;
begin
  Result := True;
end;

function TWin64BoundaryAbi.ForeignOutgoingBytes(AArgCount: Int): Int;
begin
  Result := Win64HomeBytes;
  if AArgCount > 4 then
    Result := Result + 8 * (AArgCount - 4);
end;

function TWin64BoundaryAbi.ForeignArgLoc(AIndex: Int;
  AKind: TX86ForeignArgKind; ASize: Int;
  AVariadic: Boolean): TX86ForeignArgLoc;
begin
  Result.Reg := '';
  Result.MirrorReg := '';
  Result.StackOff := 0;
  Result.ByRef := (AKind = fakRecord) and
    not ((ASize = 1) or (ASize = 2) or (ASize = 4) or (ASize = 8));
  if AIndex >= 4 then
  begin
    Result.StackOff := Win64HomeBytes + 8 * (AIndex - 4);
    Exit;
  end;
  if AKind in [fakSingle, fakDouble] then
  begin
    Result.Reg := Win64XmmArgRegs[AIndex];
    if AVariadic then
      Result.MirrorReg := Win64IntArgRegs[AIndex];
  end
  else
    Result.Reg := Win64IntArgRegs[AIndex];
end;

function TWin64BoundaryAbi.ForeignRecordResultInRax(ASize: Int): Boolean;
begin
  Result := (ASize = 1) or (ASize = 2) or (ASize = 4) or (ASize = 8);
end;

{ TElfLocalExecTls }

function TElfLocalExecTls.DirectOperand(const ASym: string): string;
begin
  Result := '%fs:' + ASym + '@tpoff';
end;

procedure TElfLocalExecTls.EmitAddress(const ASym, ADstReg: string;
  AEmit: TX86EmitProc);
begin
  AEmit(#9'movq %fs:0, ' + ADstReg);
  AEmit(#9'leaq ' + ASym + '@tpoff(' + ADstReg + '), ' + ADstReg);
end;

function TElfLocalExecTls.RewriteLine(const ALine: string;
  AEmit: TX86EmitProc): Boolean;
var
  P, Q: Int;
  Dst: string;
begin
  { `leaq %fs:X@tpoff, %reg` is never what a caller means: lea ignores the
    segment override, so it yields the bare TLS offset instead of the
    threadvar's address.  It arises wherever an address-of path formats a
    threadvar's operand; rewrite it to thread pointer plus offset. }
  Result := False;
  if Copy(ALine, 0, 10) <> #9'leaq %fs:' then Exit;
  P := Pos('@tpoff', ALine);
  Q := Pos(', ', ALine);
  if (P > 10) and (Q > P) then
  begin
    Dst := Copy(ALine, Q + 2, Length(ALine) - Q - 2);
    AEmit(#9'movq %fs:0, ' + Dst);
    AEmit(#9'leaq ' + Copy(ALine, 10, Q - 10) + '(' + Dst + '), ' + Dst);
    Result := True;
  end;
end;

{ TPeTlsModel }

const
  { The marker DirectOperand hands out, followed by the symbol and closed by
    PeTlsMarkEnd.  It never reaches the assembler: RewriteLine replaces it. }
  PeTlsMark = '%tls<';
  PeTlsMarkEnd = '>';
  { TEB.ThreadLocalStoragePointer }
  PeTebTlsArray = '%gs:88';

function TPeTlsModel.DirectOperand(const ASym: string): string;
begin
  Result := PeTlsMark + ASym + PeTlsMarkEnd;
end;

procedure TPeTlsModel.EmitAddress(const ASym, ADstReg: string;
  AEmit: TX86EmitProc);
begin
  AEmit(#9'movq ' + PeTebTlsArray + ', ' + ADstReg);
  AEmit(#9'movq (' + ADstReg + '), ' + ADstReg);
  AEmit(#9'leaq ' + ASym + '@tpoff(' + ADstReg + '), ' + ADstReg);
end;

function TPeTlsModel.RewriteLine(const ALine: string;
  AEmit: TX86EmitProc): Boolean;
var
  P, Q: Int;
  Sym, Rest: string;
begin
  Result := False;
  P := Pos(PeTlsMark, ALine);
  if P < 0 then Exit;
  Rest := Copy(ALine, P + Length(PeTlsMark),
    Length(ALine) - P - Length(PeTlsMark));
  Q := Pos(PeTlsMarkEnd, Rest);
  if Q < 0 then
    raise Exception.Create('internal: unterminated TLS operand in [' +
      ALine + ']');
  Sym := Copy(Rest, 0, Q);
  Rest := Copy(ALine, 0, P) + Sym + '@tpoff(%r11)' +
    Copy(Rest, Q + 1, Length(Rest) - Q - 1);
  { %r11 may appear only as the destination of a load or address of the
    operand itself, which the expansion leaves correct }
  if ((Pos('%r11', ALine) >= 0) and
      not (((Copy(ALine, 0, 6) = #9'leaq ') or (Copy(ALine, 0, 6) = #9'movq ')) and
           (Copy(ALine, 6, P - 6) = '') and
           (Copy(ALine, Length(ALine) - 6, 6) = ', %r11') and
           (Pos('%r11', Copy(ALine, 0, Length(ALine) - 6)) < 0))) or
     (Pos(PeTlsMark, Rest) >= 0) then
    raise Exception.Create('internal: a threadvar operand needs %r11 for ' +
      'the TLS block, which this line also uses: [' + ALine + ']');
  AEmit(#9'movq ' + PeTebTlsArray + ', %r11');
  AEmit(#9'movq (%r11), %r11');
  AEmit(Rest);
  Result := True;
end;

end.
