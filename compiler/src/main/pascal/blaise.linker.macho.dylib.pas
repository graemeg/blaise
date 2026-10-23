{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ blaise.linker.macho.dylib -- the libraries an internally linked macOS
  executable binds, beyond libSystem.

  A program that declares `external 'z'` (zlib), `external 'ssl'` (OpenSSL)
  or any other C library needs, in its image, one LC_LOAD_DYLIB per library
  -- naming the library by its INSTALL NAME, which is what dyld opens -- and
  each imported symbol bound to the library that exports it (the two-level
  namespace ordinal).  This unit finds a library from its link name and
  reads both facts:

  * an on-disk dylib (Homebrew, /usr/local, a --lib-path directory, fat or
    thin): LC_ID_DYLIB for the install name, the export trie
    (LC_DYLD_EXPORTS_TRIE or LC_DYLD_INFO_ONLY) for the symbols;
  * a text stub (.tbd) from the macOS SDK, for the system libraries that
    live only in the dyld shared cache and have no file on disk
    (/usr/lib/libz.1.dylib): its install-name and symbol lists.

  A library that re-exports others is complete only when its stub carries
  every re-exported child as a document of its own (the SDK's libSystem
  stub does).  Otherwise its symbols are bound by flat lookup (dyld
  searches every image). }
unit blaise.linker.macho.dylib;

interface

uses
  SysUtils, Classes, Generics.Collections;

type
  TMachODylib = class
  public
    LinkName:     string;    { 'z' for -lz / external 'z' }
    Path:         string;    { the file read }
    InstallName:  string;    { what LC_LOAD_DYLIB names }
    ExportsKnown: Boolean;   { False: re-exports others, bind by flat lookup }
    ExportSet:      TSet<string>;  { exported symbols, as dyld spells them }
    constructor Create;
    destructor Destroy; override;
  end;

{ True for the link names libSystem itself provides (-lc, -lm, -lpthread):
  they need no LC_LOAD_DYLIB of their own. }
function IsLibSystemLib(const ALinkName: string): Boolean;

{ The directories a library is searched in: AExtra (--lib-path) first, then
  $LIBRARY_PATH, Homebrew's and /usr/local's lib directories, and the macOS
  SDK's usr/lib (text stubs only). }
procedure BuildMachOLibSearchDirs(AExtra: TStringList; AOut: TStringList);

{ Find lib<ALinkName>.dylib or lib<ALinkName>.tbd in ADirs and read it.
  Raises EMachODylib when it is not found or cannot be read. }
function ResolveMachODylib(const ALinkName: string;
  ADirs: TStringList): TMachODylib;

{ libSystem's own export set, read from the SDK's libSystem.tbd in ADirs --
  every re-exported child (libsystem_kernel, libsystem_c, ...) included.  nil
  when no SDK stub is found or its export set is incomplete; the caller then
  cannot check a libSystem import. }
function LoadLibSystemExports(ADirs: TStringList): TMachODylib;

const
  { ChooseBindOrdinal: no bound library and not libSystem exports the name,
    so dyld would abort at launch. }
  MACHO_BIND_UNDEFINED = 0;

{ The two-level ordinal an import binds to: 2.. for the bound library in
  ADylibs that exports it, 1 for libSystem, BIND_SPECIAL_DYLIB_FLAT_LOOKUP
  when AFlatFallback (a bound library re-exports others, so its exports are
  not all known), else MACHO_BIND_UNDEFINED.  With ALibSystem nil nothing can
  be checked: the name is bound to libSystem and AUnverified is set. }
function ChooseBindOrdinal(const AName: string; ADylibs: TList<TMachODylib>;
  ALibSystem: TMachODylib; AFlatFallback: Boolean;
  out AUnverified: Boolean): Integer;

{ Fill ADylib from a dylib image (fat or thin arm64). }
procedure ReadDylibImage(const ABytes: string; ADylib: TMachODylib);
{ Fill ADylib from a text-based stub (.tbd) document. }
procedure ReadTbdStub(const AText: string; ADylib: TMachODylib);
{ Add every terminal symbol of the export trie at ABytes[AOff..AOff+ASize)
  to AOut. }
procedure ReadExportTrie(const ABytes: string; AOff, ASize: Integer;
  AOut: TSet<string>);

type
  EMachODylib = class(Exception);

implementation

uses
  uStrCompat, streams, blaise.machowriter;

const
  MH_MAGIC_64 = Integer($FEEDFACF);
  FAT_MAGIC_BE = Integer($CAFEBABE);   { read big-endian }
  CPU_TYPE_ARM64 = $0100000C;
  LC_ID_DYLIB = $0D;
  LC_REEXPORT_DYLIB = Integer($8000001F);
  LC_DYLD_INFO_ONLY = Integer($80000022);
  LC_DYLD_EXPORTS_TRIE = Integer($80000033);

constructor TMachODylib.Create;
begin
  inherited Create();
  ExportSet := TSet<string>.Create();
  ExportsKnown := True;
end;

destructor TMachODylib.Destroy;
begin
  ExportSet.Free();
  inherited Destroy();
end;

function IsLibSystemLib(const ALinkName: string): Boolean;
var
  N: string;
begin
  N := LowerCase(ALinkName);
  Result := (N = 'c') or (N = 'm') or (N = 'pthread') or (N = 'system') or
    (N = 'dl') or (N = 'dyld') or (N = 'info');
end;

function U32At(const ABuf: string; AOff: Integer): Integer;
begin
  Result := StrAt(ABuf, AOff) or (StrAt(ABuf, AOff + 1) shl 8) or
    (StrAt(ABuf, AOff + 2) shl 16) or (StrAt(ABuf, AOff + 3) shl 24);
end;

function U32BeAt(const ABuf: string; AOff: Integer): Integer;
begin
  Result := (StrAt(ABuf, AOff) shl 24) or (StrAt(ABuf, AOff + 1) shl 16) or
    (StrAt(ABuf, AOff + 2) shl 8) or StrAt(ABuf, AOff + 3);
end;

function StrZAt(const ABuf: string; AOff: Integer): string;
var
  E: Integer;
begin
  E := AOff;
  while (E < Length(ABuf)) and (StrAt(ABuf, E) <> 0) do
    E := E + 1;
  Result := Copy(ABuf, AOff, E - AOff);
end;

function ReadUleb(const ABuf: string; var AOff: Integer): Int64;
var
  B, Shift: Integer;
begin
  Result := 0;
  Shift := 0;
  repeat
    if AOff >= Length(ABuf) then
      raise EMachODylib.Create('export trie: truncated uleb128');
    B := StrAt(ABuf, AOff);
    AOff := AOff + 1;
    Result := Result or (Int64(B and $7F) shl Shift);
    Shift := Shift + 7;
  until (B and $80) = 0;
end;

procedure ReadExportTrie(const ABytes: string; AOff, ASize: Integer;
  AOut: TSet<string>);
var
  Nodes: TList<Integer>;     { pending node offsets (relative to the trie) }
  Prefixes: TList<string>;   { parallel: the symbol prefix reaching each }
  Node, P, TermSize, NChild, I, Child: Integer;
  Prefix, Edge: string;
  Steps: Integer;
begin
  if ASize <= 0 then Exit;
  if (AOff < 0) or (AOff + ASize > Length(ABytes)) then
    raise EMachODylib.Create('export trie outside the image');
  Nodes := TList<Integer>.Create();
  Prefixes := TList<string>.Create();
  try
    Nodes.Add(0);
    Prefixes.Add('');
    Steps := 0;
    while Nodes.Count > 0 do
    begin
      { a malformed trie could loop: no real one has more nodes than bytes }
      Steps := Steps + 1;
      if Steps > ASize + 1 then
        raise EMachODylib.Create('export trie: cycle');
      Node := Nodes.Get(Nodes.Count - 1);
      Prefix := Prefixes.Get(Prefixes.Count - 1);
      Nodes.Delete(Nodes.Count - 1);
      Prefixes.Delete(Prefixes.Count - 1);
      if Node >= ASize then
        raise EMachODylib.Create('export trie: node outside the trie');
      P := AOff + Node;
      TermSize := Integer(ReadUleb(ABytes, P));
      if TermSize > 0 then
        AOut.Include(Prefix);
      P := P + TermSize;
      NChild := StrAt(ABytes, P);
      P := P + 1;
      for I := 0 to NChild - 1 do
      begin
        Edge := StrZAt(ABytes, P);
        P := P + Length(Edge) + 1;
        Child := Integer(ReadUleb(ABytes, P));
        Nodes.Add(Child);
        Prefixes.Add(Prefix + Edge);
      end;
    end;
  finally
    Prefixes.Free();
    Nodes.Free();
  end;
end;

{ The arm64 slice of a fat image, or the image itself when thin. }
function ThinSlice(const ABytes: string): string;
var
  N, I, Off, Base: Integer;
begin
  Result := ABytes;
  if (Length(ABytes) < 8) or (U32BeAt(ABytes, 0) <> FAT_MAGIC_BE) then Exit;
  N := U32BeAt(ABytes, 4);
  for I := 0 to N - 1 do
  begin
    Off := 8 + I * 20;
    if Off + 20 > Length(ABytes) then Break;
    if U32BeAt(ABytes, Off) = CPU_TYPE_ARM64 then
    begin
      Base := U32BeAt(ABytes, Off + 8);
      Exit(Copy(ABytes, Base, U32BeAt(ABytes, Off + 12)));
    end;
  end;
  raise EMachODylib.Create('fat image has no arm64 slice');
end;

procedure ReadDylibImage(const ABytes: string; ADylib: TMachODylib);
var
  Img: string;
  NCmds, I, Off, Cmd, CmdSize: Integer;
begin
  Img := ThinSlice(ABytes);
  if (Length(Img) < 32) or (U32At(Img, 0) <> MH_MAGIC_64) then
    raise EMachODylib.Create('not a 64-bit Mach-O dylib');
  NCmds := U32At(Img, 16);
  Off := 32;
  for I := 0 to NCmds - 1 do
  begin
    if Off + 8 > Length(Img) then
      raise EMachODylib.Create('load commands overrun the image');
    Cmd := U32At(Img, Off);
    CmdSize := U32At(Img, Off + 4);
    if CmdSize < 8 then
      raise EMachODylib.Create('malformed load command');
    if Cmd = LC_ID_DYLIB then
      ADylib.InstallName := StrZAt(Img, Off + U32At(Img, Off + 8))
    else if Cmd = LC_REEXPORT_DYLIB then
      ADylib.ExportsKnown := False
    else if Cmd = LC_DYLD_EXPORTS_TRIE then
      ReadExportTrie(Img, U32At(Img, Off + 8), U32At(Img, Off + 12),
        ADylib.ExportSet)
    else if Cmd = LC_DYLD_INFO_ONLY then
      ReadExportTrie(Img, U32At(Img, Off + 40), U32At(Img, Off + 44),
        ADylib.ExportSet);
    Off := Off + CmdSize;
  end;
  if ADylib.InstallName = '' then
    raise EMachODylib.Create('no LC_ID_DYLIB: not a dylib');
end;

{ A symbol token of a .tbd list: up to a delimiter, quotes stripped. }
function TbdToken(const AText: string; var APos: Integer): string;
var
  B, Start, Stop: Integer;
begin
  Start := APos;
  while APos < Length(AText) do
  begin
    B := StrAt(AText, APos);
    if (B = Ord(',')) or (B = Ord(']')) or (B = Ord(' ')) or (B = 10) or
       (B = 13) or (B = 9) then
      Break;
    APos := APos + 1;
  end;
  { one Copy, not a byte-at-a-time build: libSystem's stub has ~10k
    symbols and is read on every macOS link }
  Stop := APos;
  if (Start < Stop) and (StrAt(AText, Start) = Ord('''')) then
    Start := Start + 1;
  if (Stop > Start) and (StrAt(AText, Stop - 1) = Ord('''')) then
    Stop := Stop - 1;
  Result := Copy(AText, Start, Stop - Start);
end;

{ The first index >= AFrom where ASub occurs in AText, or -1. }
function PosFrom(const ASub, AText: string; AFrom: Integer): Integer;
var
  I, J, N, M: Integer;
begin
  N := Length(AText);
  M := Length(ASub);
  I := AFrom;
  while I + M <= N do
  begin
    J := 0;
    while (J < M) and (StrAt(AText, I + J) = StrAt(ASub, J)) do
      J := J + 1;
    if J = M then
      Exit(I);
    I := I + 1;
  end;
  Result := -1;
end;

{ The quoted or bare scalar after a key at APos, to the end of the line. }
function TbdScalarAt(const AText: string; APos: Integer): string;
var
  P, Q: Integer;
begin
  P := APos;
  while (P < Length(AText)) and ((StrAt(AText, P) = Ord(' ')) or
        (StrAt(AText, P) = Ord(''''))) do
    P := P + 1;
  Q := P;
  while (Q < Length(AText)) and (StrAt(AText, Q) <> Ord('''')) and
        (StrAt(AText, Q) <> 10) and (StrAt(AText, Q) <> 13) do
    Q := Q + 1;
  Result := Trim(Copy(AText, P, Q - P));
end;

{ Every token of the '[ a, b, ... ]' list after APos (which may span lines),
  added to AOut. }
procedure ReadTbdList(const AText: string; APos: Integer; AOut: TList<string>);
var
  P, B: Integer;
  Tok: string;
begin
  P := APos;
  while (P < Length(AText)) and (StrAt(AText, P) <> Ord('[')) do
    P := P + 1;
  P := P + 1;
  while P < Length(AText) do
  begin
    B := StrAt(AText, P);
    if B = Ord(']') then Break;
    if (B = Ord(',')) or (B = Ord(' ')) or (B = 10) or (B = 13) or
       (B = 9) then
    begin
      P := P + 1;
      Continue;
    end;
    Tok := TbdToken(AText, P);
    if Tok <> '' then
      AOut.Add(Tok);
  end;
end;

{ Every '<AKey> [ ... ]' list in AText, added to AOut.  An occurrence
  preceded by '-' is skipped, so 'libraries:' does not also match
  'reexported-libraries:' and 'symbols:' does not match 'weak-symbols:'. }
procedure ReadTbdLists(const AText, AKey: string; AOut: TList<string>);
var
  P: Integer;
begin
  P := PosFrom(AKey, AText, 0);
  while P >= 0 do
  begin
    if (P = 0) or (StrAt(AText, P - 1) <> Ord('-')) then
      ReadTbdList(AText, P + Length(AKey), AOut);
    P := PosFrom(AKey, AText, P + Length(AKey));
  end;
end;

procedure ReadTbdStub(const AText: string; ADylib: TMachODylib);
const
  LISTS: array[0..2] of string = ('symbols:', 'weak-symbols:',
    'thread-local-symbols:');
var
  P, K, I: Integer;
  Names: TSet<string>;
  Toks: TList<string>;
begin
  { install-name: '/usr/lib/libz.1.dylib' -- the first one names this
    library; later documents of the stub describe re-exported children }
  P := PosFrom('install-name:', AText, 0);
  if P < 0 then
    raise EMachODylib.Create('text stub has no install-name');
  ADylib.InstallName := TbdScalarAt(AText, P + Length('install-name:'));
  { every '<list>: [ a, b, ... ]' of an exports section, in every document }
  Toks := TList<string>.Create();
  try
    for K := 0 to High(LISTS) do
      ReadTbdLists(AText, LISTS[K], Toks);
    for I := 0 to Toks.Count - 1 do
      ADylib.ExportSet.Include(Toks.Get(I));
  finally
    Toks.Free();
  end;
  { A library that re-exports others has a complete export set only when
    each re-exported child is a document of this same stub -- as the SDK's
    libSystem.B.tbd carries libsystem_kernel, libsystem_c and the rest. }
  if PosFrom('reexported-libraries:', AText, 0) >= 0 then
  begin
    Names := TSet<string>.Create();
    Toks := TList<string>.Create();
    try
      P := PosFrom('install-name:', AText, 0);
      while P >= 0 do
      begin
        Names.Include(TbdScalarAt(AText, P + Length('install-name:')));
        P := PosFrom('install-name:', AText, P + Length('install-name:'));
      end;
      ReadTbdLists(AText, 'libraries:', Toks);
      if Toks.Count = 0 then
        ADylib.ExportsKnown := False;
      for I := 0 to Toks.Count - 1 do
        if not Names.Contains(Toks.Get(I)) then
          ADylib.ExportsKnown := False;
    finally
      Toks.Free();
      Names.Free();
    end;
  end;
end;

function LoadLibSystemExports(ADirs: TStringList): TMachODylib;
begin
  Result := nil;
  try
    Result := ResolveMachODylib('System', ADirs);
  except
    on E: EMachODylib do
      Exit(nil);
  end;
  if not Result.ExportsKnown then
  begin
    Result.Free();
    Result := nil;
  end;
end;

function ChooseBindOrdinal(const AName: string; ADylibs: TList<TMachODylib>;
  ALibSystem: TMachODylib; AFlatFallback: Boolean;
  out AUnverified: Boolean): Integer;
var
  I: Integer;
begin
  AUnverified := False;
  for I := 0 to ADylibs.Count - 1 do
    if ADylibs.Get(I).ExportSet.Contains(AName) then
      Exit(I + 2);
  if (ALibSystem <> nil) and ALibSystem.ExportSet.Contains(AName) then
    Exit(1);
  if AFlatFallback then
    Exit(BIND_SPECIAL_DYLIB_FLAT_LOOKUP);
  if ALibSystem <> nil then
    Exit(MACHO_BIND_UNDEFINED);
  AUnverified := True;
  Result := 1;
end;

function ReadDylibFile(const APath: string): string;
var
  FIn: TFileInputStream;
begin
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(Result, Integer(FIn.Size()));
    if Length(Result) > 0 then
      FIn.Read(PChar(Result), Length(Result));
  finally
    FIn.Free();
  end;
end;

procedure BuildMachOLibSearchDirs(AExtra: TStringList; AOut: TStringList);
  procedure AddDir(const ADir: string);
  begin
    if (ADir <> '') and (AOut.IndexOf(ADir) < 0) then
      AOut.Add(ADir);
  end;
  procedure AddColonList(const AList: string);
  var
    Seg: string;
    K, B: Integer;
  begin
    Seg := '';
    for K := 0 to Length(AList) - 1 do
    begin
      B := StrAt(AList, K);
      if B = Ord(':') then
      begin
        AddDir(Seg);
        Seg := '';
      end
      else
        Seg := Seg + Chr(B);
    end;
    AddDir(Seg);
  end;
var
  I: Integer;
  SdkRoot: string;
begin
  if AExtra <> nil then
    for I := 0 to AExtra.Count - 1 do
      AddDir(AExtra.Strings[I]);
  AddColonList(GetEnvironmentVariable('LIBRARY_PATH'));
  AddDir('/opt/homebrew/lib');
  AddDir('/usr/local/lib');
  SdkRoot := GetEnvironmentVariable('SDKROOT');
  if SdkRoot <> '' then
    AddDir(SdkRoot + '/usr/lib');
  AddDir('/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib');
  AddDir('/Applications/Xcode.app/Contents/Developer/Platforms/' +
    'MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/lib');
end;

function ResolveMachODylib(const ALinkName: string;
  ADirs: TStringList): TMachODylib;
var
  I: Integer;
  Cand: string;
begin
  for I := 0 to ADirs.Count - 1 do
  begin
    Cand := ADirs.Strings[I] + '/lib' + ALinkName + '.dylib';
    if not FileExists(Cand) then
    begin
      Cand := ADirs.Strings[I] + '/lib' + ALinkName + '.tbd';
      if not FileExists(Cand) then Continue;
    end;
    Result := TMachODylib.Create();
    Result.LinkName := ALinkName;
    Result.Path := Cand;
    try
      if SameText(ExtractFileExt(Cand), '.tbd') then
        ReadTbdStub(ReadDylibFile(Cand), Result)
      else
        ReadDylibImage(ReadDylibFile(Cand), Result);
    except
      on E: Exception do
      begin
        Result.Free();
        raise EMachODylib.Create(Cand + ': ' + Exception(E).Message);
      end;
    end;
    Exit;
  end;
  Cand := '';
  for I := 0 to ADirs.Count - 1 do
  begin
    if I > 0 then
      Cand := Cand + ', ';
    Cand := Cand + ADirs.Strings[I];
  end;
  raise EMachODylib.Create(Format('library ''%s'' not found (searched %s); ' +
    'pass --lib-path DIR', [ALinkName, Cand]));
end;

end.
