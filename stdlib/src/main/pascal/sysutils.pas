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
// Platform constants (LineEnding, DirectorySeparator, PathSeparator) are
// defined in system.pas — they are platform fundamentals, not SysUtils
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

{ _RaiseDivByZero — raises EDivByZero('Division by zero').  Called by the
  compiler-emitted div/mod guard; not intended for direct use.  Declared in
  the interface so the code generator can reference the $SysUtils_RaiseDivByZero
  symbol. }
procedure _RaiseDivByZero;

{ StrToIntDef — convert a string to Integer; return ADefault on failure. }
function StrToIntDef(const S: string; ADefault: Integer): Integer;

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
function _StrToIntChecked(const S: string): Integer;
function _StrToInt64Checked(const S: string): Int64;

{ BoolToStr — not a compiler built-in; pure Pascal implementation }
function BoolToStr(B: Boolean; AUseBoolStrs: Boolean = False): string;

{ ExpandFileName — resolve a relative path to an absolute path.
  If APath is already absolute (starts with '/') it is returned unchanged
  after normalising redundant separators and '.' components.
  Otherwise it is resolved relative to GetCurrentDir().
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

implementation

constructor Exception.Create(AMessage: string);
begin
  Self.FMessage := AMessage
end;

procedure _RaiseDivByZero;
begin
  raise EDivByZero.Create('Division by zero')
end;

function IsValidIntStr(const S: string): Boolean;
var
  I, Len, C: Integer;
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

function StrToIntDef(const S: string; ADefault: Integer): Integer;
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

function _StrToIntChecked(const S: string): Integer;
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

{ ExpandFileName — pure Pascal path normaliser.
  Resolves '..' and '.' components without a local string array.
  The algorithm builds the result as a string, treating it as a stack:
  appending '/' + segment to push, trimming the last segment to pop. }
function ExpandFileName(const APath: string): string;
var
  Base: string;
  Len, I, SegStart, LastSlash: Integer;
  SP: PChar;
  Seg: string;
begin
  if APath = '' then
  begin
    Exit(GetCurrentDir());
  end;

  { Determine base: absolute or relative }
  if APath[0] = 47 then  { '/' }
    Base := APath
  else
    Base := GetCurrentDir() + '/' + APath;

  Len    := Length(Base);
  SP     := PChar(Base);
  Result := '';
  I      := 0;

  { Skip leading slash }
  if (Len > 0) and (SP[0] = 47) then
    I := 1;

  while I <= Len do
  begin
    SegStart := I;
    while (I < Len) and (SP[I] <> 47) do
      I := I + 1;
    if I > SegStart then
      Seg := Copy(Base, SegStart, I - SegStart)
    else
      Seg := '';
    if (Seg <> '') and (Seg <> '.') then
    begin
      if Seg = '..' then
      begin
        { Pop the last segment from Result: find the last '/' and truncate }
        LastSlash := Length(Result) - 1;
        while (LastSlash > 0) and (Result[LastSlash] <> 47) do
          LastSlash := LastSlash - 1;
        if LastSlash >= 0 then
          Result := Copy(Result, 0, LastSlash);
      end
      else
        Result := Result + '/' + Seg;
    end;
    I := I + 1;  { skip '/' }
  end;

  if Result = '' then
    Result := '/';
end;

{ PARTIAL STUB — exact compare only; see the interface note.  Correct on
  case-sensitive (Unix) file systems; needs a case-insensitive branch for
  Windows. }
function SameFileName(const S1, S2: string): Boolean;
begin
  Result := S1 = S2;
end;

end.
