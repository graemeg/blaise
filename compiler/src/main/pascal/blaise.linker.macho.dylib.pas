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

  A library that re-exports others has exports this reader does not follow;
  its symbols are then bound by flat lookup (dyld searches every image). }
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
  uStrCompat, streams;

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
  B: Integer;
begin
  Result := '';
  while APos < Length(AText) do
  begin
    B := StrAt(AText, APos);
    if (B = Ord(',')) or (B = Ord(']')) or (B = Ord(' ')) or (B = 10) or
       (B = 13) or (B = 9) then
      Break;
    if B <> Ord('''') then
      Result := Result + Chr(B);
    APos := APos + 1;
  end;
end;

procedure ReadTbdStub(const AText: string; ADylib: TMachODylib);
const
  LISTS: array[0..2] of string = ('symbols:', 'weak-symbols:',
    'thread-local-symbols:');
var
  P, K, Q, B: Integer;
  Tok: string;
begin
  { install-name: '/usr/lib/libz.1.dylib' -- the first one names this
    library; later documents of the stub describe re-exported children }
  P := Pos('install-name:', AText);
  if P < 0 then
    raise EMachODylib.Create('text stub has no install-name');
  P := P + Length('install-name:');
  while (P < Length(AText)) and ((StrAt(AText, P) = Ord(' ')) or
        (StrAt(AText, P) = Ord(''''))) do
    P := P + 1;
  Q := P;
  while (Q < Length(AText)) and (StrAt(AText, Q) <> Ord('''')) and
        (StrAt(AText, Q) <> 10) and (StrAt(AText, Q) <> 13) do
    Q := Q + 1;
  ADylib.InstallName := Trim(Copy(AText, P, Q - P));
  if Pos('reexported-libraries:', AText) >= 0 then
    ADylib.ExportsKnown := False;
  { every '<list>: [ a, b, ... ]' of an exports section }
  for K := 0 to High(LISTS) do
  begin
    P := Pos(LISTS[K], AText);
    while P >= 0 do
    begin
      P := P + Length(LISTS[K]);
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
          ADylib.ExportSet.Include(Tok);
      end;
      Q := Pos(LISTS[K], Copy(AText, P, Length(AText) - P));
      if Q < 0 then
        P := -1
      else
        P := P + Q;
    end;
  end;
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
