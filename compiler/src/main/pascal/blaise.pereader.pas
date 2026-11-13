{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.pereader;

{ PE32+ image reader (windows-x86_64-backend-design.adoc, "PE32+ linker").

  Parses the headers, the section table, and the import, base-relocation
  and TLS directories of a PE32+ image.  The Layer 0 tests read the linker's
  output with it; the export directory, needed by a native Windows link to
  check a DLL's exports, is added with that check. }

interface

uses
  SysUtils, Classes, Generics.Collections;

type
  EPeReader = class(Exception);

  TPeSection = class
  public
    Name: string;
    VirtualSize: Int;
    VirtualAddress: Int;
    SizeOfRawData: Int;
    PointerToRawData: Int;
    Characteristics: Int64;
    { the raw bytes on disk (SizeOfRawData of them) }
    Data: string;
  end;

  { One imported DLL: its symbols in address-table order, and the RVA of
    each symbol's address-table slot.  An import by ordinal reads as
    '#<ordinal>'. }
  TPeImportDll = class
  public
    Dll: string;
    Symbols: TList<string>;
    IatSlotRvas: TList<Int>;
    constructor Create;
    destructor Destroy; override;
  end;

  TPeTlsDirectory = record
    StartAddressOfRawData: Int64;
    EndAddressOfRawData: Int64;
    AddressOfIndex: Int64;
    AddressOfCallBacks: Int64;
    SizeOfZeroFill: Int;
    Characteristics: Int;
  end;

  TPeImage = class
  private
    FRaw: string;
    FDirRva: array[0..15] of Int;
    FDirSize: array[0..15] of Int;
    function ReadCStr(ARva: Int): string;
    procedure ParseImports;
    procedure ParseBaseRelocs;
    procedure ParseTls;
    procedure ParseExports;
  public
    SourceName: string;
    { COFF file header }
    Machine: Int;
    TimeDateStamp: Int64;
    Characteristics: Int;
    { optional header }
    Magic: Int;
    EntryRva: Int;
    ImageBase: Int64;
    SectionAlignment: Int;
    FileAlignment: Int;
    MajorOsVersion: Int;
    MinorOsVersion: Int;
    MajorSubsystemVersion: Int;
    MinorSubsystemVersion: Int;
    SizeOfImage: Int;
    SizeOfHeaders: Int;
    CheckSum: Int64;
    Subsystem: Int;
    DllCharacteristics: Int;
    StackReserve: Int64;
    StackCommit: Int64;
    NumberOfRvaAndSizes: Int;
    Sections: TList<TPeSection>;
    Imports: TList<TPeImportDll>;
    { the RVA of every IMAGE_REL_BASED_DIR64 location, ascending }
    BaseRelocs: TList<Int>;
    HasTls: Boolean;
    Tls: TPeTlsDirectory;
    { the names the export directory lists, in its (sorted) order }
    ExportNames: TStringList;
    constructor Create;
    destructor Destroy; override;
    function DirectoryRva(AIndex: Int): Int;
    function DirectorySize(AIndex: Int): Int;
    { The section whose virtual span holds ARva, or nil. }
    function SectionOfRva(ARva: Int): TPeSection;
    { ACount bytes of the loaded image at ARva: the headers, a section's
      raw data, or zero beyond a section's raw data.  Raises when ARva lies
      in no section. }
    function ReadRva(ARva, ACount: Int): string;
    function ReadU32(ARva: Int): Int64;
    function ReadU64(ARva: Int): Int64;
  end;

{ Parse a PE32+ image.  Raises EPeReader on malformed or unsupported input.
  Caller frees. }
function ParsePeImage(const ABytes, ASourceName: string): TPeImage;

function ReadPeImageFile(const APath: string): TPeImage;

implementation

uses
  uStrCompat, blaise.elfreader;

{ V in hexadecimal, for diagnostics. }
function HexOf(AValue: Int64): string;
const
  Digits = '0123456789ABCDEF';
var
  V: Int64;
begin
  if AValue = 0 then
  begin
    Result := '0';
    Exit;
  end;
  Result := '';
  V := AValue;
  while V <> 0 do
  begin
    Result := Copy(Digits, V and 15, 1) + Result;
    V := V shr 4;
  end;
end;

function RdU16(const ABuf: string; AOff: Int): Int;
begin
  Result := StrAt(ABuf, AOff) or (StrAt(ABuf, AOff + 1) shl 8);
end;

function RdU32(const ABuf: string; AOff: Int): Int64;
var
  R: Int64;
begin
  R := StrAt(ABuf, AOff);
  R := R or (Int64(StrAt(ABuf, AOff + 1)) shl 8);
  R := R or (Int64(StrAt(ABuf, AOff + 2)) shl 16);
  R := R or (Int64(StrAt(ABuf, AOff + 3)) shl 24);
  Result := R;
end;

function RdU64(const ABuf: string; AOff: Int): Int64;
begin
  Result := RdU32(ABuf, AOff) or (RdU32(ABuf, AOff + 4) shl 32);
end;

procedure Need(const ABuf: string; AOff, ACount: Int; const AWhat: string);
begin
  if (AOff < 0) or (AOff + ACount > Length(ABuf)) then
    raise EPeReader.Create('PE image truncated: ' + AWhat);
end;

{ ---- TPeImportDll ---- }

constructor TPeImportDll.Create;
begin
  inherited Create();
  Symbols := TList<string>.Create();
  IatSlotRvas := TList<Int>.Create();
end;

destructor TPeImportDll.Destroy;
begin
  Symbols.Free();
  IatSlotRvas.Free();
  inherited Destroy();
end;

{ ---- TPeImage ---- }

constructor TPeImage.Create;
var
  I: Int;
begin
  inherited Create();
  Sections := TList<TPeSection>.Create();
  Imports := TList<TPeImportDll>.Create();
  BaseRelocs := TList<Int>.Create();
  ExportNames := TStringList.Create();
  for I := 0 to 15 do
  begin
    FDirRva[I] := 0;
    FDirSize[I] := 0;
  end;
  HasTls := False;
end;

destructor TPeImage.Destroy;
var
  I: Int;
begin
  for I := 0 to Sections.Count - 1 do
    Sections[I].Free();
  Sections.Free();
  for I := 0 to Imports.Count - 1 do
    Imports[I].Free();
  Imports.Free();
  BaseRelocs.Free();
  ExportNames.Free();
  inherited Destroy();
end;

function TPeImage.DirectoryRva(AIndex: Int): Int;
begin
  Result := FDirRva[AIndex];
end;

function TPeImage.DirectorySize(AIndex: Int): Int;
begin
  Result := FDirSize[AIndex];
end;

function TPeImage.SectionOfRva(ARva: Int): TPeSection;
var
  I: Int;
  S: TPeSection;
begin
  Result := nil;
  for I := 0 to Sections.Count - 1 do
  begin
    S := Sections[I];
    if (ARva >= S.VirtualAddress) and
       (ARva < S.VirtualAddress + S.VirtualSize) then
    begin
      Result := S;
      Exit;
    end;
  end;
end;

function TPeImage.ReadRva(ARva, ACount: Int): string;
var
  S: TPeSection;
  Off, Avail: Int;
begin
  if ACount <= 0 then
  begin
    Result := '';
    Exit;
  end;
  if ARva + ACount <= SizeOfHeaders then
  begin
    Result := Copy(FRaw, ARva, ACount);
    Exit;
  end;
  S := SectionOfRva(ARva);
  if (S = nil) or (ARva + ACount > S.VirtualAddress + S.VirtualSize) then
    raise EPeReader.Create(SourceName + ': RVA $' + HexOf(ARva) +
      ' (+' + IntToStr(ACount) + ') lies outside every section');
  Off := ARva - S.VirtualAddress;
  Avail := Length(S.Data) - Off;
  if Avail < 0 then
    Avail := 0;
  if Avail > ACount then
    Avail := ACount;
  Result := Copy(S.Data, Off, Avail);
  while Length(Result) < ACount do
    Result := Result + #0;
end;

function TPeImage.ReadU32(ARva: Int): Int64;
begin
  Result := RdU32(ReadRva(ARva, 4), 0);
end;

function TPeImage.ReadU64(ARva: Int): Int64;
begin
  Result := RdU64(ReadRva(ARva, 8), 0);
end;

function TPeImage.ReadCStr(ARva: Int): string;
var
  S: TPeSection;
  Off, Start: Int;
begin
  S := SectionOfRva(ARva);
  if S = nil then
    raise EPeReader.Create(SourceName + ': string at RVA $' +
      HexOf(ARva) + ' lies outside every section');
  Start := ARva - S.VirtualAddress;
  Off := Start;
  while (Off < Length(S.Data)) and (StrAt(S.Data, Off) <> 0) do
    Inc(Off);
  Result := Copy(S.Data, Start, Off - Start);
end;

procedure TPeImage.ParseImports;
var
  Desc, Lookup, Iat, NameRva, Slot: Int;
  Entry: Int64;
  D: TPeImportDll;
begin
  if FDirRva[1] = 0 then Exit;
  Desc := FDirRva[1];
  while True do
  begin
    Lookup := ReadU32(Desc);
    NameRva := ReadU32(Desc + 12);
    Iat := ReadU32(Desc + 16);
    if (Lookup = 0) and (NameRva = 0) and (Iat = 0) then Break;
    if Lookup = 0 then
      Lookup := Iat;
    D := TPeImportDll.Create();
    Imports.Add(D);
    D.Dll := ReadCStr(NameRva);
    Slot := 0;
    while True do
    begin
      Entry := ReadU64(Lookup + Slot * 8);
      if Entry = 0 then Break;
      if Entry < 0 then
        { IMAGE_ORDINAL_FLAG64: import by ordinal }
        D.Symbols.Add('#' + IntToStr(Entry and $FFFF))
      else
        D.Symbols.Add(ReadCStr((Entry and $7FFFFFFF) + 2));
      D.IatSlotRvas.Add(Iat + Slot * 8);
      Inc(Slot);
    end;
    Desc := Desc + 20;
  end;
end;

procedure TPeImage.ParseBaseRelocs;
var
  Off, Stop, Page, Size, I, E: Int;
begin
  if FDirRva[5] = 0 then Exit;
  Off := FDirRva[5];
  Stop := Off + FDirSize[5];
  while Off < Stop do
  begin
    Page := ReadU32(Off);
    Size := ReadU32(Off + 4);
    if (Size < 8) or (Size mod 4 <> 0) then
      raise EPeReader.Create(SourceName +
        ': malformed base-relocation block at RVA $' + HexOf(Off));
    for I := 0 to (Size - 8) div 2 - 1 do
    begin
      E := RdU16(ReadRva(Off + 8 + I * 2, 2), 0);
      case E shr 12 of
        0: ;   { IMAGE_REL_BASED_ABSOLUTE: padding }
        10: BaseRelocs.Add(Page + (E and $FFF));
      else
        raise EPeReader.Create(SourceName +
          ': unsupported base-relocation type ' + IntToStr(E shr 12));
      end;
    end;
    Off := Off + Size;
  end;
end;

procedure TPeImage.ParseTls;
var
  R: Int;
begin
  if FDirRva[9] = 0 then Exit;
  R := FDirRva[9];
  HasTls := True;
  Tls.StartAddressOfRawData := ReadU64(R);
  Tls.EndAddressOfRawData := ReadU64(R + 8);
  Tls.AddressOfIndex := ReadU64(R + 16);
  Tls.AddressOfCallBacks := ReadU64(R + 24);
  Tls.SizeOfZeroFill := ReadU32(R + 32);
  Tls.Characteristics := ReadU32(R + 36);
end;

{ IMAGE_EXPORT_DIRECTORY: NumberOfNames at 24, AddressOfNames (an array of
  name RVAs) at 32. }
procedure TPeImage.ParseExports;
var
  Dir, Count, Names, I: Int;
begin
  Dir := FDirRva[0];
  if (Dir = 0) or (FDirSize[0] = 0) then
    Exit;
  Count := Int(ReadU32(Dir + 24));
  Names := Int(ReadU32(Dir + 32));
  for I := 0 to Count - 1 do
    ExportNames.Add(ReadCStr(Int(ReadU32(Names + I * 4))));
end;

function ParsePeImage(const ABytes, ASourceName: string): TPeImage;
var
  Img: TPeImage;
  Pe, Opt, SecTab, NumSecs, OptSize, I, P, NameEnd: Int;
  S: TPeSection;
begin
  Need(ABytes, 0, $40, 'DOS header');
  if Copy(ABytes, 0, 2) <> 'MZ' then
    raise EPeReader.Create(ASourceName + ': not a PE image (no MZ)');
  Pe := RdU32(ABytes, $3C);
  Need(ABytes, Pe, 24, 'COFF header');
  if Copy(ABytes, Pe, 4) <> 'PE'#0#0 then
    raise EPeReader.Create(ASourceName + ': no PE signature');
  Img := TPeImage.Create();
  try
    Img.SourceName := ASourceName;
    Img.FRaw := ABytes;
    Img.Machine := RdU16(ABytes, Pe + 4);
    NumSecs := RdU16(ABytes, Pe + 6);
    Img.TimeDateStamp := RdU32(ABytes, Pe + 8);
    OptSize := RdU16(ABytes, Pe + 20);
    Img.Characteristics := RdU16(ABytes, Pe + 22);
    Opt := Pe + 24;
    Need(ABytes, Opt, OptSize, 'optional header');
    Img.Magic := RdU16(ABytes, Opt);
    if Img.Magic <> $20B then
      raise EPeReader.Create(ASourceName + ': not PE32+ (magic $' +
        HexOf(Img.Magic) + ')');
    Img.EntryRva := RdU32(ABytes, Opt + 16);
    Img.ImageBase := RdU64(ABytes, Opt + 24);
    Img.SectionAlignment := RdU32(ABytes, Opt + 32);
    Img.FileAlignment := RdU32(ABytes, Opt + 36);
    Img.MajorOsVersion := RdU16(ABytes, Opt + 40);
    Img.MinorOsVersion := RdU16(ABytes, Opt + 42);
    Img.MajorSubsystemVersion := RdU16(ABytes, Opt + 48);
    Img.MinorSubsystemVersion := RdU16(ABytes, Opt + 50);
    Img.SizeOfImage := RdU32(ABytes, Opt + 56);
    Img.SizeOfHeaders := RdU32(ABytes, Opt + 60);
    Img.CheckSum := RdU32(ABytes, Opt + 64);
    Img.Subsystem := RdU16(ABytes, Opt + 68);
    Img.DllCharacteristics := RdU16(ABytes, Opt + 70);
    Img.StackReserve := RdU64(ABytes, Opt + 72);
    Img.StackCommit := RdU64(ABytes, Opt + 80);
    Img.NumberOfRvaAndSizes := RdU32(ABytes, Opt + 108);
    for I := 0 to 15 do
      if I < Img.NumberOfRvaAndSizes then
      begin
        Img.FDirRva[I] := RdU32(ABytes, Opt + 112 + I * 8);
        Img.FDirSize[I] := RdU32(ABytes, Opt + 116 + I * 8);
      end;
    SecTab := Opt + OptSize;
    Need(ABytes, SecTab, NumSecs * 40, 'section table');
    for I := 0 to NumSecs - 1 do
    begin
      P := SecTab + I * 40;
      S := TPeSection.Create();
      Img.Sections.Add(S);
      NameEnd := 0;
      while (NameEnd < 8) and (StrAt(ABytes, P + NameEnd) <> 0) do
        Inc(NameEnd);
      S.Name := Copy(ABytes, P, NameEnd);
      S.VirtualSize := RdU32(ABytes, P + 8);
      S.VirtualAddress := RdU32(ABytes, P + 12);
      S.SizeOfRawData := RdU32(ABytes, P + 16);
      S.PointerToRawData := RdU32(ABytes, P + 20);
      S.Characteristics := RdU32(ABytes, P + 36);
      if S.SizeOfRawData > 0 then
      begin
        Need(ABytes, S.PointerToRawData, S.SizeOfRawData,
          'section ' + S.Name);
        S.Data := Copy(ABytes, S.PointerToRawData, S.SizeOfRawData);
      end;
    end;
    Img.ParseImports();
    Img.ParseBaseRelocs();
    Img.ParseTls();
    Img.ParseExports();
  except
    Img.Free();
    raise;
  end;
  Result := Img;
end;

function ReadPeImageFile(const APath: string): TPeImage;
begin
  Result := ParsePeImage(ReadWholeFile(APath), APath);
end;

end.
