{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit SysUtils;

// Blaise RTL — SysUtils unit.
//
// Provides the Exception base class and the BoolToStr helper.
//
// Platform constants (LineEnding, DirectorySeparator, PathSeparator) belong
// to the implicit System unit — they are platform fundamentals, not SysUtils
// concerns.  Blaise does not carry the Delphi/FPC legacy aliases
// (sLineBreak, PathDelim).
//
// Functions that are already compiler built-ins (FileExists, DeleteFile,
// RenameFile, SetCurrentDir, ExtractFileExt, IntToStr, StrToInt, Format,
// UpperCase, LowerCase, Trim, CompareStr, CompareText, SameText, etc.) are
// deliberately absent from this interface.  Re-declaring them here would
// shadow the built-ins and produce a duplicate-identifier error at compile time.

interface

type
  Exception = class
    FMessage: string;
    constructor Create(AMessage: string);
    property Message: string read FMessage;
  end;

  EInOutError = class(Exception)
  end;

  EConvertError = class(Exception)
  end;

  { Raised by the collection types for a programming error the container
    cannot paper over: removing or inspecting an element that is not there
    (TStack.Pop/Peek and TQueue.Dequeue/Peek on an empty container,
    TDictionary.GetItem for a key that is absent).  Matches Delphi, where
    EListError lives in System.Classes and covers the same ground.

    Pascal has no checked/unchecked split, so this is "unchecked" in Java's
    sense automatically — nothing is declared and no caller is forced to
    handle it.  Guard with IsEmpty / ContainsKey, or use the Try* variants,
    if you would rather branch than catch. }
  EListError = class(Exception)
  end;

  { Raised by integer `div`/`mod` when the divisor is zero.  The compiler
    emits a divisor==0 guard before each integer division that calls
    _RaiseDivByZero (below) when SysUtils is in scope; without SysUtils the
    division traps in hardware (SIGFPE) as before.  Matches Delphi, where
    EDivByZero lives in System.SysUtils. }
  EDivByZero = class(Exception)
  end;

  { Raised by `Obj as TSomeClass` (and `as` to an interface) when the
    object is not an instance of the target.  The compiler routes a failed
    cast to _RaiseInvalidCast (below) when SysUtils is in scope; without
    SysUtils it is a fatal runtime error as before.  Matches Delphi, where
    EInvalidCast lives in System.SysUtils. }
  EInvalidCast = class(Exception)
  end;

{ _RaiseDivByZero — raises EDivByZero('Division by zero').  Called by the
  compiler-emitted div/mod guard; not intended for direct use.  Declared in
  the interface so the code generator can reference the $SysUtils_RaiseDivByZero
  symbol. }
procedure _RaiseDivByZero;

{ _RaiseInvalidCast — raises EInvalidCast('Invalid class typecast').  Called
  by the compiler-emitted check behind a failed `as`; not intended for direct
  use.  Declared in the interface so the code generator can reference it. }
procedure _RaiseInvalidCast;

{ StrToIntDef — convert a string to Integer; return ADefault on failure. }
function StrToIntDef(const S: string; ADefault: Int): Int;

{ StrToInt64Def — convert a string to Int64; return ADefault on failure. }
function StrToInt64Def(const S: string; ADefault: Int64): Int64;

{ _StrToIntChecked / _StrToInt64Checked — validating variants of the StrToInt /
  StrToInt64 built-ins.  They raise EConvertError('...') when S is empty or
  contains trailing non-digit characters, matching Delphi/FPC semantics.  The
  code generator rewrites a StrToInt/StrToInt64 call to reference the
  $SysUtils__StrToIntChecked symbol when SysUtils is in scope; without SysUtils
  the lenient runtime _StrToInt is called (parses what it can, never raises).
  Not intended for direct use — declared in the interface so codegen can link
  them. }
function _StrToIntChecked(const S: string): Int;
function _StrToInt64Checked(const S: string): Int64;

{ BoolToStr — not a compiler built-in; pure Pascal implementation }
function BoolToStr(B: Boolean; AUseBoolStrs: Boolean = False): string;

{ ExtractFileDrive — the drive part of APath: 'C:' for 'C:\dir' or 'C:dir',
  '\\server\share' for a UNC path, '' otherwise.  Only where the target's
  DirectorySeparator is '\' (Windows): elsewhere 'C:' is an ordinary file
  name and the result is always ''. }
function ExtractFileDrive(const APath: string): string;

{ ExpandFileName — resolve a relative path to an absolute path.
  If APath is already absolute (starts with a separator, or a drive and a
  separator on Windows) it is returned unchanged after normalising redundant
  separators and '.' components, and with the target's DirectorySeparator
  between components.  Otherwise it is resolved relative to GetCurrentDir().
  Note: '..' segments are removed by simple text processing; symlinks are
  not resolved (unlike POSIX realpath).  This matches Delphi/FPC behaviour
  on paths that do not traverse symlinks. }
function ExpandFileName(const APath: string): string;

{ SameFileName — compare two file names for equality.

  PARTIAL STUB: an exact, case-sensitive string comparison.  This is correct
  only on case-sensitive file systems (Unix); case-insensitive platforms
  (Windows) would need the names folded before comparing.  Blaise has no
  platform-variance facility yet — system.pas hardcodes DirectorySeparator,
  PathSeparator and LineEnding to their Unix values — so there is nothing to
  key the case-folding on.  When a FileNameCaseSensitive constant lands
  alongside the other platform constants, add the case-insensitive branch
  here under that guard. }
function SameFileName(const S1, S2: string): Boolean;

{ The environment the program was started with, one 'NAME=VALUE' string per
  variable: GetEnvironmentString(0) .. GetEnvironmentString(Count - 1), and
  '' for an index out of range.  FPC's names, 0-based as everything in
  Blaise.  GetEnvironmentVariable reads one variable by name.  Blaise has no
  setenv, so the start-up environment is the program's environment; a
  change made through a C binding shows in GetEnvironmentVariable, not
  here. }
function GetEnvironmentVariableCount(): Int;
function GetEnvironmentString(AIndex: Int): string;

implementation

function _EnvVector: Pointer; external name '_EnvVector';

{ Slot AIndex of the environment vector, or nil past its end. }
function EnvEntry(AIndex: Int): PChar;
var
  V: Pointer;
  I: Int;
  Slot: ^Pointer;
begin
  Result := nil;
  V := _EnvVector();
  if (V = nil) or (AIndex < 0) then Exit;
  for I := 0 to AIndex do
  begin
    Slot := Pointer(UInt(V) + UInt(I * SizeOf(Pointer)));
    if Slot^ = nil then Exit;
  end;
  Slot := Pointer(UInt(V) + UInt(AIndex * SizeOf(Pointer)));
  Result := PChar(Slot^);
end;

function GetEnvironmentVariableCount(): Int;
begin
  Result := 0;
  while EnvEntry(Result) <> nil do
    Result := Result + 1;
end;

function GetEnvironmentString(AIndex: Int): string;
var
  P: PChar;
begin
  P := EnvEntry(AIndex);
  if P = nil then
    Result := ''
  else
    Result := string(P);
end;

constructor Exception.Create(AMessage: string);
begin
  Self.FMessage := AMessage
end;

procedure _RaiseDivByZero;
begin
  raise EDivByZero.Create('Division by zero')
end;

procedure _RaiseInvalidCast;
begin
  raise EInvalidCast.Create('Invalid class typecast')
end;

function IsValidIntStr(const S: string): Boolean;
var
  I, Len, C: Int;
begin
  Len := Length(S);
  if Len = 0 then
    Exit(False);
  I := 0;
  C := Ord(S[0]);
  if (C = 43) or (C = 45) then
  begin
    I := 1;
    if I >= Len then
      Exit(False);
  end;
  if Ord(S[I]) = 36 then
  begin
    I := I + 1;
    if I >= Len then
      Exit(False);
    while I < Len do
    begin
      C := Ord(S[I]);
      if not (((C >= 48) and (C <= 57))
           or ((C >= 65) and (C <= 70))
           or ((C >= 97) and (C <= 102))) then
        Exit(False);
      I := I + 1;
    end;
    Exit(True);
  end;
  while I < Len do
  begin
    C := Ord(S[I]);
    if (C < 48) or (C > 57) then
      Exit(False);
    I := I + 1;
  end;
  Result := True;
end;

function StrToIntDef(const S: string; ADefault: Int): Int;
begin
  if not IsValidIntStr(S) then
    Exit(ADefault);
  Result := StrToInt(S);
end;

function StrToInt64Def(const S: string; ADefault: Int64): Int64;
begin
  if not IsValidIntStr(S) then
    Exit(ADefault);
  Result := StrToInt64(S);
end;

function _StrToIntChecked(const S: string): Int;
begin
  if not IsValidIntStr(S) then
    raise EConvertError.Create('"' + S + '" is not a valid integer value');
  Result := StrToInt(S);
end;

function _StrToInt64Checked(const S: string): Int64;
begin
  if not IsValidIntStr(S) then
    raise EConvertError.Create('"' + S + '" is not a valid integer value');
  Result := StrToInt64(S);
end;

function BoolToStr(B: Boolean; AUseBoolStrs: Boolean): string;
begin
  if B then
    Result := 'True'
  else
    Result := 'False'
end;

{ Whether byte I of S separates path components: '/' on every target, and
  the target's DirectorySeparator (so '\' too on Windows). }
function IsPathSepAt(const S: string; I: Int): Boolean;
begin
  Result := (I >= 0) and (I < Length(S)) and
    ((Copy(S, I, 1) = '/') or (Copy(S, I, 1) = DirectorySeparator));
end;

function ExtractFileDrive(const APath: string): string;
var
  I, N: Int;
  C: string;
begin
  Result := '';
  if DirectorySeparator <> '\' then
    Exit;
  if (Length(APath) >= 2) and (Copy(APath, 1, 1) = ':') then
  begin
    C := UpperCase(Copy(APath, 0, 1));
    if (C >= 'A') and (C <= 'Z') then
      Exit(Copy(APath, 0, 2));
  end;
  if IsPathSepAt(APath, 0) and IsPathSepAt(APath, 1) then
  begin
    { \\server\share: up to the separator after the share }
    I := 2;
    N := 0;
    while I < Length(APath) do
    begin
      if IsPathSepAt(APath, I) then
      begin
        Inc(N);
        if N = 2 then
          Break;
      end;
      Inc(I);
    end;
    Result := Copy(APath, 0, I);
  end;
end;

{ ExpandFileName — pure Pascal path normaliser.
  Resolves '..' and '.' components without a local string array.  The
  drive (Windows) is split off first; the rest is built as a string treated
  as a stack: appending a separator + segment to push, trimming the last
  segment to pop. }
function ExpandFileName(const APath: string): string;
var
  Base, Drive, Rest, Cwd, Sep: string;
  Len, I, SegStart, LastSep: Int;
  Seg: string;
begin
  if APath = '' then
  begin
    Exit(GetCurrentDir());
  end;
  Sep := DirectorySeparator;

  { Determine the drive and the base: absolute or relative }
  Drive := ExtractFileDrive(APath);
  if Drive <> '' then
  begin
    Rest := Copy(APath, Length(Drive), Length(APath) - Length(Drive));
    if IsPathSepAt(Rest, 0) or IsPathSepAt(Drive, 0) then
      Base := Rest
    else
    begin
      { drive-relative ('C:dir'): against the current directory when it is
        on that drive, else the drive's root }
      Cwd := GetCurrentDir();
      if SameText(ExtractFileDrive(Cwd), Drive) then
        Base := Copy(Cwd, Length(Drive), Length(Cwd) - Length(Drive)) +
          '/' + Rest
      else
        Base := '/' + Rest;
    end;
  end
  else if IsPathSepAt(APath, 0) then
  begin
    Base := APath;
    Drive := ExtractFileDrive(GetCurrentDir());
  end
  else
  begin
    Cwd := GetCurrentDir();
    Drive := ExtractFileDrive(Cwd);
    Base := Copy(Cwd, Length(Drive), Length(Cwd) - Length(Drive)) + '/' + APath;
  end;

  Len    := Length(Base);
  Result := '';
  I      := 0;

  { Skip a leading separator }
  if IsPathSepAt(Base, 0) then
    I := 1;

  while I <= Len do
  begin
    SegStart := I;
    while (I < Len) and not IsPathSepAt(Base, I) do
      I := I + 1;
    if I > SegStart then
      Seg := Copy(Base, SegStart, I - SegStart)
    else
      Seg := '';
    if (Seg <> '') and (Seg <> '.') then
    begin
      if Seg = '..' then
      begin
        { Pop the last segment from Result: find the last separator and
          truncate }
        LastSep := Length(Result) - 1;
        while (LastSep > 0) and (Copy(Result, LastSep, 1) <> Sep) do
          LastSep := LastSep - 1;
        if LastSep >= 0 then
          Result := Copy(Result, 0, LastSep);
      end
      else
        Result := Result + Sep + Seg;
    end;
    I := I + 1;  { skip the separator }
  end;

  if Result = '' then
    Result := Sep;
  Result := Drive + Result;
end;

{ PARTIAL STUB — exact compare only; see the interface note.  Correct on
  case-sensitive (Unix) file systems; needs a case-insensitive branch for
  Windows. }
function SameFileName(const S1, S2: string): Boolean;
begin
  Result := S1 = S2;
end;

end.
