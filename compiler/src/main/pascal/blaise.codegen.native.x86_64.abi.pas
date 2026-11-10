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

type
  { Emits one line of assembly through the backend, so the backend's stream
    observers (stack-depth tracking, register-promotion rewrites) see it. }
  TX86EmitProc = procedure(const ALine: string) of object;

  { The calling convention where control crosses into or out of foreign
    code (design decision D1: the internal convention is System V on every
    target).  M0 exposes only the queries; the foreign-call and foreign-entry
    lowerings are added with the first adapter that differs (Win64, M2). }
  TX86BoundaryAbi = class
  public
    { True when frames of a page or more must be probed in the prologue. }
    function NeedsStackProbe: Boolean; virtual; abstract;
    { True when a C-convention routine differs from the internal one. }
    function ForeignDiffers: Boolean; virtual; abstract;
  end;

  { System V AMD64: the C convention IS the internal convention, and the
    stack grows on demand, so neither probing nor translation is needed. }
  TSysVBoundaryAbi = class(TX86BoundaryAbi)
  public
    function NeedsStackProbe: Boolean; override;
    function ForeignDiffers: Boolean; override;
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
    { The backend's peephole hook: when ALine takes the address of a
      DirectOperand (`leaq <operand>, %reg`), emit the real per-thread address
      sequence instead and return True; otherwise emit nothing and return
      False. }
    function RewriteAddressOf(const ALine: string;
      AEmit: TX86EmitProc): Boolean; virtual; abstract;
  end;

  { ELF local-exec: %fs holds the thread pointer; a threadvar is at a
    negative link-time offset from it (R_X86_64_TPOFF32). }
  TElfLocalExecTls = class(TX86TlsModel)
  public
    function DirectOperand(const ASym: string): string; override;
    procedure EmitAddress(const ASym, ADstReg: string;
      AEmit: TX86EmitProc); override;
    function RewriteAddressOf(const ALine: string;
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

function TElfLocalExecTls.RewriteAddressOf(const ALine: string;
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

end.
