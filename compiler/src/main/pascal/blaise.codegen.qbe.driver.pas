{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.qbe.driver;

{ TBackendDriver subclass for the QBE backend.

  Owns the answers Blaise.pas used to compute via `if Backend = bkQBE`:
  which ICodeGen to instantiate (TCodeGenQBE) and its knob setup, the IR
  file extension (.ssa), and the qbe -> .s -> cc lowering/link steps.

  Architecture follows Andrew Haines' unify_backend_interface proposal.

  Pull this unit into Blaise.pas's uses clause; the initialization block
  registers the singleton driver. }

interface

uses
  Classes,
  blaise.codegen,
  blaise.codegen.qbe,
  blaise.codegen.target,   { TargetHasQBEBackend / TargetName }
  blaise.codegen.driver;

type
  TQBEBackendDriver = class(TBackendDriver)
  public
    function Kind: TBackendKind; override;
    function Name: string; override;
    function IRFileExt: string; override;
    function SupportsIncremental: Boolean; override;
    function SupportsWarmCache: Boolean; override;
    function CreateCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function LowerToObject(const AIRFile, AObjFile: string;
      AOpts: TBackendOpts; const AIfaceBytes: string): string; override;
    function LinkProgram(const AIRFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string; override;
    function ClaimsEmitIR: Boolean; override;
  protected
    { qbe AIRFile -> AAsmFile.  Returns '' on success. }
    function LowerToAsm(const AIRFile, AAsmFile: string;
      AOpts: TBackendOpts): string;
    { Scan AIRFile for '# WEAKSYM <sym>' markers and append matching
      '.weak <sym>' directives to AAsmFile (generic-instance dedup,
      BUGS.md BUG-004). }
    procedure ApplyWeakSymbols(const AIRFile, AAsmFile: string);
  end;

implementation

uses
  SysUtils,
  uStrCompat,
  uToolchain;

function TQBEBackendDriver.Kind: TBackendKind;
begin
  Result := bkQBE;
end;

function TQBEBackendDriver.Name: string;
begin
  Result := 'qbe';
end;

function TQBEBackendDriver.IRFileExt: string;
begin
  Result := '.ssa';
end;

function TQBEBackendDriver.ClaimsEmitIR: Boolean;
begin
  { QBE owns the --emit-ir text: the fixpoint check and the RTL Makefile
    depend on byte-identical QBE IR. }
  Result := True;
end;


function TQBEBackendDriver.SupportsIncremental: Boolean;
begin
  Result := True;
end;

function TQBEBackendDriver.SupportsWarmCache: Boolean;
begin
  { QBE-emitted .o files participate in the warm cache: each parallel
    unit worker writes a .o + embedded .bif, uUnitLoader discovers them
    on the next compile and hash-matches against the .pas to decide
    whether to skip recompilation. }
  Result := True;
end;

function TQBEBackendDriver.CreateCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenQBE;
begin
  CG := TCodeGenQBE.Create();
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  { TCodeGenQBE has no target knob; AOpts.Target only affects the
    link step. }
  Result := CG;
end;

function TQBEBackendDriver.CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenQBE;
begin
  { Same as CreateCodeGen plus SetExportAll(True) so sibling units in
    the link can resolve this unit's globals.  The knob is applied here
    so TCompileWorker relies on ICodeGen alone — no backend casts. }
  CG := TCodeGenQBE.Create();
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  CG.SetExportAll(True);
  CG.SetSuppressSystemDefs(True);
  Result := CG;
end;

function TQBEBackendDriver.LowerToAsm(const AIRFile, AAsmFile: string;
  AOpts: TBackendOpts): string;
var
  Args: TStringList;
  Msg: string;
  ExitCode: Integer;
begin
  Result := '';
  Args := TStringList.Create();
  try
    Args.Add('-o');
    Args.Add(AAsmFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess(ResolveQBE().Path, Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
  begin
    Result := 'qbe error (exit ' + IntToStr(ExitCode) + '): ' + Msg;
    Exit;
  end;
  ApplyWeakSymbols(AIRFile, AAsmFile);
end;

procedure TQBEBackendDriver.ApplyWeakSymbols(const AIRFile,
  AAsmFile: string);
var
  IR:     TStringList;
  AsmSL:  TStringList;
  I:      Integer;
  Line:   string;
  Syms:   TStringList;
  Sym:    string;
begin
  { QBE IR cannot express symbol binding.  The QBE codegen marks every
    generic-instance symbol with a '# WEAKSYM <sym>' comment in the .ssa;
    this post-step appends '.weak <sym>' directives to the qbe-produced .s
    (gas: a later .weak demotes an earlier .globl), so any number of objects
    in a link may carry the identical bare-named instance copy and the
    linker keeps one (BUGS.md BUG-004). }
  Syms := TStringList.Create();
  IR := TStringList.Create();
  try
    IR.LoadFromFile(AIRFile);
    for I := 0 to IR.Count - 1 do
    begin
      Line := IR.Strings[I];
      if Copy(Line, 0, 10) = '# WEAKSYM ' then
      begin
        Sym := Trim(StrCopyTail(Line, 10));
        if (Sym <> '') and (Syms.IndexOf(Sym) < 0) then
          Syms.Add(Sym);
      end;
    end;
    if Syms.Count = 0 then Exit;
    AsmSL := TStringList.Create();
    try
      AsmSL.LoadFromFile(AAsmFile);
      for I := 0 to Syms.Count - 1 do
        AsmSL.Add('.weak ' + Syms.Strings[I]);
      AsmSL.SaveToFile(AAsmFile);
    finally
      AsmSL.Free();
    end;
  finally
    IR.Free();
    Syms.Free();
  end;
end;

function TQBEBackendDriver.LowerToObject(const AIRFile, AObjFile: string;
  AOpts: TBackendOpts; const AIfaceBytes: string): string;
var
  AsmFile: string;
  Args: TStringList;
  Msg: string;
  ExitCode: Integer;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  Result := Self.LowerToAsm(AIRFile, AsmFile, AOpts);
  if Result <> '' then Exit;

  Args := TStringList.Create();
  try
    Args.Add('-c');
    Args.Add('-o');
    Args.Add(AObjFile);
    Args.Add(AsmFile);
    ExitCode := RunProcess(ResolveLinker(AOpts.Target).Path, Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
    Exit('cc -c error (exit ' + IntToStr(ExitCode) + '): ' + Msg);

  DeleteFile(AsmFile);
end;

function TQBEBackendDriver.LinkProgram(const AIRFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  AsmFile: string;
begin
  { Refuse a target QBE was never ported to, by name, instead of producing an
    executable that links and then crashes before main.  Gated HERE rather than
    in ValidateOptions because that runs unconditionally, for flag-combination
    rules: blocking it there also blocked --emit-ir, which is harmless (it prints
    IR text, produces no artefact) and is what scripts/fixpoint.sh compares.
    Emitting IR stays allowed; producing an unrunnable BINARY does not.
    See TargetHasQBEBackend. }
  if not TargetHasQBEBackend(AOpts.Target) then
    Exit('the qbe backend does not support target ' +
      TargetName(AOpts.Target) + ' — use the native backend (the default; ' +
      'omit --backend qbe)');
  { The qbe backend links through the system cc, which always produces a
    dynamic libc-linked binary.  --static used to be silently IGNORED on
    this path; reject it loudly instead — freestanding binaries are a
    native-backend (internal linker) feature. }
  if AOpts.LinkMode = lmStatic then
    Exit('--static: the qbe backend links via the system toolchain and ' +
      'cannot produce freestanding binaries — use the native backend ' +
      '(the default; omit --backend qbe)');
  AsmFile := ChangeFileExt(AIRFile, '.s');
  Result := Self.LowerToAsm(AIRFile, AsmFile, AOpts);
  if Result <> '' then Exit;
  Result := Self.LinkViaToolchain(AsmFile, AOutputFile, AOpts, AExtraObjects);
  { The intermediate .s is this driver's own artefact.  Keep it on link
    failure as a debugging aid (matches the pre-driver behaviour). }
  if Result = '' then
    DeleteFile(AsmFile);
end;

initialization
  RegisterDriver(TQBEBackendDriver.Create());

end.
