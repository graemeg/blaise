{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.driver;

{ TBackendDriver subclass for the native backend.

  Differences from the QBE driver:

    * The "IR" the native codegen emits IS the target .s assembly text,
      so IRFileExt is '.s' and no lowering tool runs before the link.

    * Linking honours --assembler: external (default) feeds the .s to
      the cc driver; internal assembles in-process via AssembleToObject
      and only shells out for the final link.

    * SupportsIncremental / SupportsWarmCache are True: the native pipeline
      writes a self-contained per-unit .o (its assembly, assembled to an object,
      with the .bif iface embedded) so the --incremental worker pool runs on the
      native backend directly.  Unit objects are compiled in separate-compilation
      mode (FSeparateCompile) — they omit the once-per-program TObject/
      TCustomAttribute system defs (the program object provides the single
      global definition) and carry their own file-local string literals.

  Architecture follows Andrew Haines' unify_backend_interface proposal.

  Pull this unit into Blaise.pas's uses clause; the initialization block
  registers the singleton driver. }

interface

uses
  Classes,
  blaise.codegen,
  blaise.codegen.native,
  blaise.codegen.driver;

type
  TNativeBackendDriver = class(TBackendDriver)
  public
    function Kind: TBackendKind; override;
    function Name: string; override;
    function IRFileExt: string; override;
    function CreateCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function LinkProgram(const AIRFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string; override;
    function LowerToObject(const AIRFile, AObjFile: string;
      AOpts: TBackendOpts; const AIfaceBytes: string): string; override;

    { Per-unit parallel compilation + warm cache: native emits a self-contained
      object per unit (.s assembled to .o, plus an embedded .bif), the same as
      QBE.  Enabling these routes the --incremental worker pool through the
      native backend instead of falling back to QBE. }
    function SupportsIncremental: Boolean; override;
    function SupportsWarmCache: Boolean; override;
    function SupportsLibrary(const ATarget: TTargetDesc): Boolean; override;

    { --- Option contract: owns --assembler/--linker internal|external --- }
    function AcceptOption(const AFlag, ANextArg: string;
      AOpts: TBackendOpts): TOptionAccept; override;
    procedure DescribeOptions(ALines: TStringList); override;
    function ValidateOptions(AOpts: TBackendOpts): string; override;

  private
    function LinkViaMachOLinker(const AObjFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string;
    function LinkViaInternalLinker(const AObjFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string;
    { EnsureRTLObjects is inherited from TBackendDriver — both the native
      internal linker and the cc link line build the RTL the same way. }
  end;

implementation

uses
  SysUtils, Classes,
  uStrCompat,
  uToolchain,
  blaise.codegen.toolkit,
  blaise.codegen.target,
  blaise.assembler.x86_64,
  blaise.assembler.arm64,
  blaise.elfreader,
  blaise.linker.elf,
  blaise.linker.macho;

{ In-process assembly, keyed on the target CPU: x86-64 text goes to the
  ELF-emitting assembler, arm64 text to the Mach-O-emitting one.  Each
  raises its own exception class; callers catch plain Exception. }
procedure AssembleForTarget(const AAsmText, AObjFile: string;
  const ATarget: TTargetDesc; const AIfaceBytes: string);
begin
  { AIfaceBytes is Mach-O only — see TBackendOpts.IfaceBytes.  The x86-64/ELF
    path embeds the .bif post-hoc through uElfObject and is handed '' here. }
  if ATarget.CPU = cpuArm64 then
    AssembleArm64ToObject(AAsmText, AObjFile, AIfaceBytes)
  else
    AssembleToObject(AAsmText, AObjFile);
end;

function TNativeBackendDriver.Kind: TBackendKind;
begin
  Result := bkNative;
end;

function TNativeBackendDriver.Name: string;
begin
  Result := 'native';
end;

function TNativeBackendDriver.IRFileExt: string;
begin
  Result := '.s';
end;

function TNativeBackendDriver.CreateCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenNative;
begin
  CG := TCodeGenNative.Create();
  CG.SetTarget(AOpts.Target);
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  Result := CG;
end;

function TNativeBackendDriver.CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenNative;
begin
  { Same as CreateCodeGen; the native backend already emits unit globals,
    methods, vtables and typeinfo with global (.globl) visibility, so sibling
    units in the link resolve this unit's symbols without an extra export knob. }
  CG := TCodeGenNative.Create();
  CG.SetTarget(AOpts.Target);
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  CG.SetSeparateCompile(True);   { suppress per-unit system defs (link collision) }
  Result := CG;
end;

function TNativeBackendDriver.SupportsIncremental: Boolean;
begin
  Result := True;
end;

function TNativeBackendDriver.SupportsWarmCache: Boolean;
begin
  Result := True;
end;

function TNativeBackendDriver.SupportsLibrary(const ATarget: TTargetDesc): Boolean;
begin
  { Shared-object emission is ELF-only: the internal linker writes ET_DYN with
    .init_array load constructors and .dynsym exports.  A Mach-O target needs
    __mod_init_func and LC_DYLD_INFO exports instead, which are not written
    yet — refuse rather than emit an ELF object for a Darwin target. }
  Result := TargetUsesElf(ATarget);
end;

function TNativeBackendDriver.LowerToObject(const AIRFile, AObjFile: string;
  AOpts: TBackendOpts; const AIfaceBytes: string): string;
var
  Args:     TStringList;
  AsmText:  TStringList;
  Msg:      string;
  ExitCode: Integer;
begin
  Result := '';
  { For the native backend the "IR file" already IS the x86-64 assembly the
    unit codegen emitted — there is no qbe step.  Assemble it to a relocatable
    object: in-process when --assembler internal, else via the toolchain's
    `cc -c`. }
  if AOpts.UseInternalAsm then
  begin
    AsmText := TStringList.Create();
    try
      try
        AsmText.LoadFromFile(AIRFile);
        AssembleForTarget(AsmText.Text, AObjFile, AOpts.Target,
          AIfaceBytes);
      except
        on E: EAssembler do
          Exit('Internal assembler error: ' + Exception(E).Message);
        on E: Exception do
          Exit('Internal assembler error [' + Exception(E).ClassName + ']: ' +
            Exception(E).Message);
      end;
    finally
      AsmText.Free();
    end;
    Exit;
  end;
  Args := TStringList.Create();
  try
    Args.Add('-c');
    { Force assembler language: the worker writes the IR to a name like
      '<unit>.o.s.tmp', whose extension cc would not recognise as assembly. }
    Args.Add('-x');
    Args.Add('assembler');
    Args.Add('-o');
    Args.Add(AObjFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess(ResolveLinker(AOpts.Target).Path, Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
    Result := 'cc -c error (exit ' + IntToStr(ExitCode) + '): ' + Msg;
end;

{ Map a link-library name (as it appears in `external 'lib'` or the codegen's
  required-libs list) to the SONAME the dynamic loader records in DT_NEEDED.
  The external cc linker resolves `-l<name>` to lib<name>.so at link time and
  the resulting binary carries the library's real SONAME; the internal linker
  writes DT_NEEDED itself, so it must name the versioned SONAME directly.  Known
  system libs get their canonical SONAME; anything else falls back to the
  conventional unversioned 'lib<name>.so' (a dev symlink, matching -l<name>). }
function LinkLibSoname(const ALibName: string): string;
begin
  if SameText(ALibName, 'pthread') then Result := 'libpthread.so.0'
  else if SameText(ALibName, 'm')  then Result := 'libm.so.6'
  else if SameText(ALibName, 'dl') then Result := 'libdl.so.2'
  else if SameText(ALibName, 'rt') then Result := 'librt.so.1'
  else if SameText(ALibName, 'c')  then Result := 'libc.so.6'
  else Result := 'lib' + ALibName + '.so';
end;

{ ------------------------------------------------------------------------
  Shared-library resolution for the internal linker (GH #188).

  The external cc/ld linker resolves `-l<name>` itself: it searches the lib
  dirs, follows the `lib<name>.so` dev symlink to the versioned `.so.N`, reads
  its DT_SONAME for the DT_NEEDED entry, and expands GNU ld linker scripts
  (`INPUT(...)`/`GROUP(...)`) that stand in for a real `.so`.  The internal
  linker previously did NONE of this — it string-guessed `lib<name>.so` and
  wrote that verbatim as DT_NEEDED.  On distros where `lib<name>.so` is a
  linker script (Debian/Ubuntu ncurses: a 31-byte `INPUT(libncurses.so.6
  -ltinfo)`) the loader then tries to mmap the 31-byte text file as a shared
  object and dies with "file too short".

  These helpers replicate what ld does: find the file, and either read its
  DT_SONAME (real ELF ET_DYN) or parse the linker script and resolve the libs
  it names.  The resolved SONAMEs are appended to ANeeded (deduped).  On any
  miss the caller falls back to the old string guess so behaviour is never
  worse than before.
  ------------------------------------------------------------------------ }

{ Little-endian byte readers over a raw byte string (0-based offsets).  Local
  to this unit so they do not collide with the private RdU* in blaise.elfreader
  / blaise.machoreader.  StrAt(S, I) is the 0-based ordinal byte accessor. }
function DrvU16(const ABuf: string; AOff: Integer): Integer;
begin
  Result := (StrAt(ABuf, AOff) and $FF)
         or ((StrAt(ABuf, AOff + 1) and $FF) shl 8);
end;

function DrvU32(const ABuf: string; AOff: Integer): Integer;
begin
  Result := (StrAt(ABuf, AOff) and $FF)
         or ((StrAt(ABuf, AOff + 1) and $FF) shl 8)
         or ((StrAt(ABuf, AOff + 2) and $FF) shl 16)
         or ((StrAt(ABuf, AOff + 3) and $FF) shl 24);
end;

function DrvU64(const ABuf: string; AOff: Integer): Int64;
var Lo, Hi: Int64;
begin
  Lo := Int64(DrvU32(ABuf, AOff)) and $FFFFFFFF;
  Hi := Int64(DrvU32(ABuf, AOff + 4)) and $FFFFFFFF;
  Result := Lo or (Hi shl 32);
end;

{ NUL-terminated string at a 0-based offset. }
function DrvStrZ(const ABuf: string; AOff: Integer): string;
var P, N: Integer;
begin
  Result := '';
  P := AOff;
  N := Length(ABuf);
  while (P < N) and (StrAt(ABuf, P) <> 0) do
  begin
    Result := Result + Chr(StrAt(ABuf, P));
    P := P + 1;
  end;
end;

{ Default ELF shared-library search directories, plus any from LibPaths /
  LD_LIBRARY_PATH / LIBRARY_PATH.  Matches the common Linux multiarch layout;
  a --lib-path entry (AExtra) takes precedence. }
procedure BuildLibSearchDirs(AExtra: TStringList; AOut: TStringList);
  procedure AddColonList(const AList: string);
  var Seg: string; K, N, B: Integer;
  begin
    if AList = '' then Exit;
    Seg := '';
    N := Length(AList);
    K := 0;                     { string bytes are 0-based here (Blaise) }
    while K < N do
    begin
      B := StrAt(AList, K);
      if B = Ord(':') then
      begin
        if (Seg <> '') and (AOut.IndexOf(Seg) < 0) then AOut.Add(Seg);
        Seg := '';
      end
      else
        Seg := Seg + Chr(B);
      K := K + 1;
    end;
    if (Seg <> '') and (AOut.IndexOf(Seg) < 0) then AOut.Add(Seg);
  end;
var
  I: Integer;
begin
  if AExtra <> nil then
    for I := 0 to AExtra.Count - 1 do
      if (AExtra.Strings[I] <> '') and (AOut.IndexOf(AExtra.Strings[I]) < 0) then
        AOut.Add(AExtra.Strings[I]);
  AddColonList(GetEnvironmentVariable('LD_LIBRARY_PATH'));
  AddColonList(GetEnvironmentVariable('LIBRARY_PATH'));
  if AOut.IndexOf('/lib/x86_64-linux-gnu') < 0 then AOut.Add('/lib/x86_64-linux-gnu');
  if AOut.IndexOf('/usr/lib/x86_64-linux-gnu') < 0 then AOut.Add('/usr/lib/x86_64-linux-gnu');
  if AOut.IndexOf('/usr/local/lib') < 0 then AOut.Add('/usr/local/lib');
  if AOut.IndexOf('/lib') < 0 then AOut.Add('/lib');
  if AOut.IndexOf('/usr/lib') < 0 then AOut.Add('/usr/lib');
end;

{ Read DT_SONAME from an ET_DYN ELF image.  Returns '' if the bytes are not a
  little-endian ELFCLASS64 shared object or carry no DT_SONAME. }
function ReadElfSoname(const ABytes: string): string;
var
  EType, PhEntSize, PhNum, I: Integer;
  PhOff, EntOff, DynOff, DynSz, StrTabVaddr, StrTabOff, DEnt, DTag, DVal: Int64;
  PType: Integer;
  StrLoad: Int64;
  SonameOff: Int64;
begin
  Result := '';
  { ELF header: magic 7F 45 4C 46, ELFCLASS64=2, ELFDATA2LSB=1. }
  if Length(ABytes) < 64 then Exit;
  if DrvU32(ABytes, 0) <> $464C457F then Exit;   { 7F 'E' 'L' 'F' LE }
  if DrvU16(ABytes, 4) and $FF <> 2 then Exit;   { EI_CLASS = ELFCLASS64 }
  EType := DrvU16(ABytes, 16);
  if (EType <> 3) then Exit;                     { ET_DYN }
  PhOff := DrvU64(ABytes, 32);
  PhEntSize := DrvU16(ABytes, 54);
  PhNum := DrvU16(ABytes, 56);
  if (PhOff <= 0) or (PhNum <= 0) or (PhEntSize < 56) then Exit;
  { Locate PT_DYNAMIC (p_type=2): p_type@0, p_offset@8, p_filesz@32. }
  DynOff := 0; DynSz := 0;
  for I := 0 to PhNum - 1 do
  begin
    EntOff := PhOff + Int64(I) * PhEntSize;
    if EntOff + 56 > Length(ABytes) then Exit;
    PType := DrvU32(ABytes, EntOff);
    if PType = 2 then
    begin
      DynOff := DrvU64(ABytes, EntOff + 8);
      DynSz := DrvU64(ABytes, EntOff + 32);
      Break;
    end;
  end;
  if (DynOff <= 0) or (DynSz <= 0) then Exit;
  { First pass: find DT_STRTAB (tag 5) vaddr and DT_SONAME (tag 14) offset.
    Each Elf64_Dyn entry is 16 bytes: d_tag (i64) then d_val/d_ptr (u64). }
  StrTabVaddr := -1; SonameOff := -1;
  DEnt := DynOff;
  while DEnt + 16 <= DynOff + DynSz do
  begin
    if DEnt + 16 > Length(ABytes) then Break;
    DTag := DrvU64(ABytes, DEnt);
    DVal := DrvU64(ABytes, DEnt + 8);
    if DTag = 0 then Break;                       { DT_NULL }
    if DTag = 5 then StrTabVaddr := DVal          { DT_STRTAB }
    else if DTag = 14 then SonameOff := DVal;     { DT_SONAME }
    DEnt := DEnt + 16;
  end;
  if (StrTabVaddr < 0) or (SonameOff < 0) then Exit;
  { Translate the DT_STRTAB vaddr to a file offset via the PT_LOAD segment
    that contains it (p_vaddr@16, p_offset@8, p_filesz@32). }
  StrTabOff := -1;
  for I := 0 to PhNum - 1 do
  begin
    EntOff := PhOff + Int64(I) * PhEntSize;
    if DrvU32(ABytes, EntOff) <> 1 then Continue;  { PT_LOAD }
    StrLoad := DrvU64(ABytes, EntOff + 16);        { p_vaddr }
    DynSz := DrvU64(ABytes, EntOff + 32);          { reuse: p_filesz }
    if (StrTabVaddr >= StrLoad) and (StrTabVaddr < StrLoad + DynSz) then
    begin
      StrTabOff := DrvU64(ABytes, EntOff + 8) + (StrTabVaddr - StrLoad);
      Break;
    end;
  end;
  if StrTabOff < 0 then Exit;
  if StrTabOff + SonameOff >= Length(ABytes) then Exit;
  Result := DrvStrZ(ABytes, StrTabOff + SonameOff);
end;

{ True if the file text is a GNU ld script (not an ELF binary) that names input
  libraries.  Extracts the INPUT(...)/GROUP(...) tokens into ATokens: bare
  `-lNAME` become NAME (re-resolved as a library) and explicit `libX.so[.N]`
  filenames are kept verbatim. }
function ParseLinkerScript(const AText: string; ATokens: TStringList): Boolean;
var
  I, N, B: Integer;
  Tok: string;
  InParen: Boolean;
begin
  Result := False;
  ATokens.Clear();
  { An ELF object starts with the 0x7F 'E' 'L' 'F' magic; a linker script is
    plain text.  Bail out fast on binaries.  StrPos is 0-based and returns -1
    when the substring is absent. }
  if (Length(AText) >= 4) and (DrvU32(AText, 0) = $464C457F) then Exit;
  if (StrPos('INPUT', AText) < 0) and (StrPos('GROUP', AText) < 0) then Exit;
  N := Length(AText);
  I := 0;                       { string bytes are 0-based here (Blaise) }
  InParen := False;
  Tok := '';
  while I < N do
  begin
    B := StrAt(AText, I);
    if B = Ord('(') then
    begin
      InParen := True; Tok := '';
    end
    else if B = Ord(')') then
    begin
      if Tok <> '' then ATokens.Add(Tok);
      Tok := ''; InParen := False;
    end
    else if InParen then
    begin
      if (B = Ord(' ')) or (B = 9) or (B = 10) or (B = 13) or (B = Ord(',')) then
      begin
        if Tok <> '' then ATokens.Add(Tok);
        Tok := '';
      end
      else
        Tok := Tok + Chr(B);
    end;
    I := I + 1;
  end;
  Result := ATokens.Count > 0;
end;

{ Find lib<AName>.so on the search path; also probe the versioned dev names.
  Returns the resolved path or '' if not found. }
function FindLibFile(const AName: string; ADirs: TStringList): string;
var
  I: Integer;
  Cand: string;
begin
  Result := '';
  for I := 0 to ADirs.Count - 1 do
  begin
    Cand := ADirs.Strings[I] + '/lib' + AName + '.so';
    if FileExists(Cand) then Exit(Cand);
  end;
  { Fallbacks: a bare .so may be absent but .so.N present (no dev package). }
  for I := 0 to ADirs.Count - 1 do
  begin
    Cand := ADirs.Strings[I] + '/lib' + AName + '.so.6';
    if FileExists(Cand) then Exit(Cand);
  end;
end;

{ Resolve one -l<name> library into DT_NEEDED soname(s), appending to ANeeded
  (deduped).  Follows linker scripts recursively.  AVisited guards against
  cyclic INPUT() references.  Falls back to the string guess on any miss. }
procedure ResolveLibNeeded(const AName: string; ADirs, ANeeded,
  AVisited: TStringList);
var
  Path, Bytes, Soname, Tok, InnerName: string;
  Scr: TStringList;
  J: Integer;
begin
  if AVisited.IndexOf(AName) >= 0 then Exit;
  AVisited.Add(AName);
  Path := FindLibFile(AName, ADirs);
  if Path = '' then
  begin
    { Not found on the path — keep the historical guess so previously-working
      links (e.g. a lib present only at runtime) are unaffected. }
    Soname := LinkLibSoname(AName);
    if ANeeded.IndexOf(Soname) < 0 then ANeeded.Add(Soname);
    Exit;
  end;
  Bytes := ReadWholeFile(Path);
  Soname := ReadElfSoname(Bytes);
  if Soname <> '' then
  begin
    if ANeeded.IndexOf(Soname) < 0 then ANeeded.Add(Soname);
    Exit;
  end;
  { Not a readable ELF ET_DYN — try a linker script. }
  Scr := TStringList.Create();
  try
    if ParseLinkerScript(Bytes, Scr) then
    begin
      for J := 0 to Scr.Count - 1 do
      begin
        Tok := Scr.Strings[J];
        { String helpers here are 0-based: StrPos returns -1 when absent,
          StrAt indexes bytes, StrCopyFrom(S, From, Count) copies. }
        if (Length(Tok) >= 2) and (StrAt(Tok, 0) = Ord('-'))
           and (StrAt(Tok, 1) = Ord('l')) then
          { A bare -lNAME reference — resolve it as its own library. }
          ResolveLibNeeded(StrCopyTail(Tok, 2), ADirs, ANeeded, AVisited)
        else
        begin
          { A file token — possibly an absolute path (a GROUP() script names
            /lib/.../libm.so.6) or a keyword (AS_NEEDED, OUTPUT_FORMAT).  Take
            the basename and act on it only if it is a libX.so[.N]. }
          Tok := ExtractFileName(Tok);
          if (StrPos('lib', Tok) = 0) and (StrPos('.so', Tok) >= 0) then
          begin
            if StrPos('.so.', Tok) >= 0 then
            begin
              { Already a versioned SONAME — use it directly. }
              if ANeeded.IndexOf(Tok) < 0 then ANeeded.Add(Tok);
            end
            else
              { An unversioned libX.so (another dev symlink / script) — recurse
                on its base name so its own SONAME / script is resolved. }
              ResolveLibNeeded(StrCopyFrom(Tok, 3, StrPos('.so', Tok) - 3),
                ADirs, ANeeded, AVisited);
          end;
        end;
      end;
    end
    else
    begin
      { Neither ELF nor a recognisable script — fall back. }
      Soname := LinkLibSoname(AName);
      if ANeeded.IndexOf(Soname) < 0 then ANeeded.Add(Soname);
    end;
  finally
    Scr.Free();
  end;
end;

function TNativeBackendDriver.LinkViaMachOLinker(
  const AObjFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  Lk: TMachOLinker;
  RTLObjs: TStringList;
  I: Integer;
begin
  Result := '';
  RTLObjs := TStringList.Create();
  try
    { same implicit-RTL machinery as the ELF path: the darwin unit list
      (BuildRTLUnitList) has no start unit — LC_MAIN enters _main }
    Result := Self.EnsureRTLObjects(AOpts, True, AExtraObjects, RTLObjs);
    if Result <> '' then Exit;
    Lk := TMachOLinker.Create();
    try
      try
        Lk.AddObjectFile(AObjFile);
        if AExtraObjects <> nil then
          for I := 0 to AExtraObjects.Count - 1 do
            Lk.AddObjectFile(AExtraObjects.Strings[I]);
        for I := 0 to RTLObjs.Count - 1 do
          Lk.AddObjectFile(RTLObjs.Strings[I]);
        Lk.LinkToFile('_main', AOutputFile);
        MakeFileExecutable(AOutputFile);
      except
        on E: Exception do
          Result := 'macho linker error [' + Exception(E).ClassName
            + ']: ' + Exception(E).Message;
      end;
    finally
      Lk.Free();
    end;
  finally
    RTLObjs.Free();
  end;
end;

function TNativeBackendDriver.LinkViaInternalLinker(
  const AObjFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Toolkit: TTargetToolkit;
  LinkTarget: TLinkTarget;
  RTLObjs: TStringList;
  LibDirs, Needed, Visited: TStringList;
  I: Integer;
begin
  Result := '';

  { Build the linker with the resolved target's TLinkTarget so the emitted ELF
    carries the right EI_OSABI / machine / load base for AOpts.Target — without
    this the internal linker always produced a Linux-shaped ELF regardless of
    --target.  The toolkit is the single source of per-target link facts
    (docs/native-target-architecture.adoc). }
  Toolkit := ResolveToolkit(AOpts.Target);
  if Toolkit = nil then
    Exit('internal linker: no toolkit registered for target ' +
      TargetName(AOpts.Target));
  { A toolkit without ELF link facts is a Mach-O target — hand the whole
    link to the Mach-O linker (same RTL-object machinery, different
    container). }
  LinkTarget := Toolkit.MakeLinkTarget();
  if LinkTarget = nil then
    Exit(Self.LinkViaMachOLinker(AObjFile, AOutputFile, AOpts,
      AExtraObjects));

  { Build the implicit RTL objects from source (cached beside the compiler).
    Every Blaise program emits calls to RTL symbols (_SetArgs, _BlaiseGetMem,
    _start, ARC/string/exception helpers, …) as undefined externals; these
    objects supply them.  Replaces the pre-built blaise_rtl.a — the RTL is now
    compiled by the compiler itself. }
  RTLObjs := TStringList.Create();
  try
    { Native internal linker: Blaise owns the entry point, so include
      runtime.start (its bare _start).  In --static mode EnsureRTLObjects swaps
      runtime.start for the freestanding runtime.start.static.<os> and adds the
      syscall + cstub leaves, so AIncludeStartup is irrelevant there.  Pass the
      program's prebuilt deps so an RTL unit it compiled itself is not supplied
      twice. }
    Result := Self.EnsureRTLObjects(AOpts, True, AExtraObjects, RTLObjs);
    if Result <> '' then Exit;

    { TLinker.Create(ATarget) borrows the target — created at the nil gate
      above; freed in the finally below. }
    Lk := TLinker.Create(LinkTarget);
    try
      try
        { --static: freestanding non-PIE ET_EXEC, no libc/PT_INTERP (the kernel
          leaf supplies open/read/write/... + _start).  Default: dynamic PIE
          linked against libc.  A freestanding target (FreeBSD, Strategy B) has
          no libc to link against, so it is ALWAYS static regardless of the
          --static flag — the kernel leaf is the only libc it gets. }
        Lk.SetDynamic(not (AOpts.Static or TargetIsFreestanding(AOpts.Target)));

        { Demand-driven shared-library dependencies (from `external 'lib'`
          declarations and codegen-required libs like 'm').  A DYNAMIC binary
          gets one DT_NEEDED per lib, mapped to its SONAME; the loader resolves
          the symbols at run time.  A STATIC / freestanding binary has NO
          .dynamic section and no libc to link against, so these are ignored —
          on those paths threads come from the freestanding kernel leaf, not
          libpthread, and float math is emitted inline.  This replaces the old
          hard rejection of any LinkLibs: the internal linker now handles the
          same -l<name> deps the external cc linker does.

          Each -l<name> is resolved on the lib search path to its real SONAME
          (or the SONAMEs a GNU ld linker script names) rather than the bare
          string-guessed lib<name>.so — see ResolveLibNeeded (GH #188). }
        if Lk.IsDynamic() and (AOpts.LinkLibs <> nil) then
        begin
          LibDirs := TStringList.Create();
          Needed := TStringList.Create();
          Visited := TStringList.Create();
          try
            BuildLibSearchDirs(AOpts.LibPaths, LibDirs);
            for I := 0 to AOpts.LinkLibs.Count - 1 do
              ResolveLibNeeded(AOpts.LinkLibs.Strings[I], LibDirs, Needed,
                Visited);
            for I := 0 to Needed.Count - 1 do
              Lk.AddNeededLib(Needed.Strings[I]);
          finally
            Visited.Free();
            Needed.Free();
            LibDirs.Free();
          end;
        end;

        Obj := ReadElfObjectFile(AObjFile);
        Lk.AddOwnedObject(Obj);

        if AExtraObjects <> nil then
          for I := 0 to AExtraObjects.Count - 1 do
          begin
            Obj := ReadElfObjectFile(AExtraObjects.Strings[I]);
            Lk.AddOwnedObject(Obj);
          end;

        { The RTL objects — including _start (runtime.start) and the implicit
          runtime symbols — built from source above. }
        for I := 0 to RTLObjs.Count - 1 do
        begin
          Obj := ReadElfObjectFile(RTLObjs.Strings[I]);
          Lk.AddOwnedObject(Obj);
        end;

        Lk.Link('_start', AOutputFile);
      except
        on E: Exception do
          Result := 'internal linker error [' + Exception(E).ClassName + ']: ' +
            Exception(E).Message;
      end;
    finally
      Lk.Free();
    end;
  finally
    RTLObjs.Free();
    LinkTarget.Free();
  end;
end;

function TNativeBackendDriver.LinkProgram(const AIRFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  ObjFile: string;
  AsmText: TStringList;
begin
  if AOpts.UseInternalAsm then
  begin
    { --assembler internal: assemble the .s text in-process, then drive
      only the final link.  The IR file IS the assembly the top-program
      codegen emitted. }
    ObjFile := ChangeFileExt(AOutputFile, '.o');
    AsmText := TStringList.Create();
    try
      try
        AsmText.LoadFromFile(AIRFile);
        AssembleForTarget(AsmText.Text, ObjFile, AOpts.Target, '');
      except
        on E: EAssembler do
          Exit('Internal assembler error: ' + Exception(E).Message);
        on E: Exception do
          Exit('Internal assembler error [' + Exception(E).ClassName + ']: ' +
            Exception(E).Message);
      end;
    finally
      AsmText.Free();
    end;
    if AOpts.UseInternalLinker then
      Result := Self.LinkViaInternalLinker(ObjFile, AOutputFile, AOpts,
        AExtraObjects)
    else
      Result := Self.LinkViaToolchain(ObjFile, AOutputFile, AOpts, AExtraObjects);
    if Result = '' then
      DeleteFile(ObjFile);
  end
  else if AOpts.UseInternalLinker then
  begin
    { External assembler + internal linker: assemble to .o via cc -c,
      then link with the internal linker. }
    ObjFile := ChangeFileExt(AOutputFile, '.o');
    Result := Self.LowerToObject(AIRFile, ObjFile, AOpts, '');
    if Result <> '' then Exit;
    Result := Self.LinkViaInternalLinker(ObjFile, AOutputFile, AOpts,
      AExtraObjects);
    if Result = '' then
      DeleteFile(ObjFile);
  end
  else
    { External assembler + external linker: the cc driver assembles and
      links the .s in one invocation.  The IR file is owned by the
      caller — no cleanup here. }
    Result := Self.LinkViaToolchain(AIRFile, AOutputFile, AOpts, AExtraObjects);
end;

function TNativeBackendDriver.AcceptOption(const AFlag, ANextArg: string;
  AOpts: TBackendOpts): TOptionAccept;
begin
  if AFlag = '--assembler' then
  begin
    AOpts.UseInternalAsm := (ANextArg = 'internal');
    AOpts.AssemblerExplicit := True;
    AOpts.AssemblerChoiceBad :=
      (ANextArg <> 'internal') and (ANextArg <> 'external');
    Result := oaConsumedValue;
  end
  else if AFlag = '--linker' then
  begin
    AOpts.UseInternalLinker := (ANextArg = 'internal');
    AOpts.LinkerExplicit := True;
    AOpts.LinkerChoiceBad :=
      (ANextArg <> 'internal') and (ANextArg <> 'external');
    Result := oaConsumedValue;
  end
  else
    Result := oaUnknown;
end;

procedure TNativeBackendDriver.DescribeOptions(ALines: TStringList);
begin
  ALines.Add(FormatFlagLine('--assembler <id>',
    'internal | external (default: internal)'));
  ALines.Add(FormatFlagLine('--linker <id>',
    'internal | external (default: internal)'));
end;

function TNativeBackendDriver.ValidateOptions(AOpts: TBackendOpts): string;
begin
  Result := '';
  if AOpts.AssemblerChoiceBad then
    Result := '--assembler must be ''internal'' or ''external'''
  else if AOpts.LinkerChoiceBad then
    Result := '--linker must be ''internal'' or ''external''';

  if not AOpts.AssemblerExplicit then
    AOpts.UseInternalAsm := True;
  if not AOpts.LinkerExplicit then
    AOpts.UseInternalLinker := True;
end;

initialization
  RegisterDriver(TNativeBackendDriver.Create());

end.
