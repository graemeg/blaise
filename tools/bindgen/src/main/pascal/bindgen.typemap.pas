{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — clang qualType string → Blaise type name.

  Mapping notes (LP64 targets, which is all Blaise targets):
    - C char (any signedness) maps to Byte: Blaise has no signed 8-bit
      type.  Size and ABI class are identical; only the arithmetic
      interpretation differs, which bindings rarely rely on.
    - Function pointers degrade to Pointer in slice 1.
    - Pointers to named C types synthesise a 'PName = ^Name' alias,
      collected on the mapper for the emitter to declare. }

unit Bindgen.TypeMap;

interface

uses
  SysUtils, StrUtils, generics.collections;

type
  { One synthetic pointer alias the mapper invented, e.g. PDisplay = ^Display. }
  TPtrAlias = class
  public
    Name: string;      { PDisplay }
    Target: string;    { Display }
    constructor Create(const AName, ATarget: string);
  end;

  { One synthesised procedural type for an inline (non-typedef'd)
    function-pointer parameter, e.g.
      TXIfEvent_predicate = function(a0: PDisplay; a1: PXEvent; a2: XPointer): Integer; }
  TProcTypeDecl = class
  public
    Name: string;      { TXIfEvent_predicate }
    Decl: string;      { the right-hand side, without trailing ';' }
    constructor Create(const AName, ADecl: string);
  end;

  TTypeMapper = class
  private
    FPtrAliases: TList<TPtrAlias>;
    FPtrSeen: TSet<string>;
    FProcTypes: TList<TProcTypeDecl>;
    FProcBySig: TDictionary<string, string>;  { decl string → type name }
    FProcNames: TSet<string>;
    function MapPointer(const APointee: string): string;
    procedure RegisterAlias(const AName, ATarget: string);
  public
    constructor Create;
    { Map a clang qualType to a Blaise type name.  Returns '' for void.
      Function-pointer types degrade to Pointer here — use MapCallback
      in contexts where a synthesised procedural type is wanted. }
    function Map(const AQualType: string): string;
    { Render a function-pointer qualType as a Blaise procedural-type
      right-hand side ('function(a0: X): Y' / 'procedure(...)').
      Returns '' when it cannot be represented (variadic, unparsable). }
    function FnPtrDecl(const AQualType: string): string;
    { Like Map, but a representable function pointer synthesises a
      named procedural type 'T<AHint>' (deduped by signature, so
      look-alike callbacks share one type) and returns its name. }
    function MapCallback(const AQualType, AHint: string): string;
    { Pointer-to-mapped-type: maps APointee and registers/returns the
      'P<Name>' alias.  Used for union member accessors. }
    function MapPointerTo(const APointee: string): string;
    property PtrAliases: TList<TPtrAlias> read FPtrAliases;
    property ProcTypes: TList<TProcTypeDecl> read FProcTypes;
  end;

{ Strip leading const/volatile/restrict qualifiers and struct/union/enum
  tag keywords, and a trailing ' const' (as in 'char *const'). }
function StripQualifiers(const AType: string): string;

{ Map a C builtin type name to its Blaise primitive, or '' if AType is
  not a builtin.  Expects qualifiers already stripped. }
function MapBuiltin(const AType: string): string;

implementation

function StripPrefixWord(const S, AWord: string): string;
begin
  if StartsStr(AWord + ' ', S) then
    Result := Trim(MidStr(S, Length(AWord) + 1, Length(S)))
  else
    Result := S;
end;

function StripQualifiers(const AType: string): string;
var
  Prev: string;
begin
  Result := Trim(AType);
  repeat
    Prev := Result;
    Result := StripPrefixWord(Result, 'const');
    Result := StripPrefixWord(Result, 'volatile');
    Result := StripPrefixWord(Result, 'restrict');
    Result := StripPrefixWord(Result, 'struct');
    Result := StripPrefixWord(Result, 'union');
    Result := StripPrefixWord(Result, 'enum');
    { Trailing qualifiers: 'char *const', and glibc's 'char *restrict'
      (restrict binds to the pointer, written as a suffix). }
    if EndsStr(' const', Result) then
      Result := Trim(LeftStr(Result, Length(Result) - 6));
    if EndsStr('restrict', Result) then
      Result := Trim(LeftStr(Result, Length(Result) - 8));
  until Result = Prev;
end;

function MapBuiltin(const AType: string): string;
begin
  Result := '';
  if AType = 'void' then Exit;
  if (AType = 'char') or (AType = 'signed char') or (AType = 'unsigned char') then
    Result := 'Byte'
  else if (AType = 'short') or (AType = 'short int') or
          (AType = 'signed short') or (AType = 'signed short int') then
    Result := 'SmallInt'
  else if (AType = 'unsigned short') or (AType = 'unsigned short int') then
    Result := 'Word'
  else if (AType = 'int') or (AType = 'signed int') or (AType = 'signed') then
    Result := 'Integer'
  else if (AType = 'unsigned int') or (AType = 'unsigned') then
    Result := 'Cardinal'
  else if (AType = 'long') or (AType = 'long int') or
          (AType = 'signed long') or (AType = 'signed long int') or
          (AType = 'long long') or (AType = 'long long int') or
          (AType = 'signed long long') or (AType = 'signed long long int') then
    Result := 'Int64'
  else if (AType = 'unsigned long') or (AType = 'unsigned long int') or
          (AType = 'unsigned long long') or (AType = 'unsigned long long int') then
    Result := 'UInt64'
  else if AType = 'float' then
    Result := 'Single'
  else if AType = 'double' then
    Result := 'Double'
  else if (AType = '_Bool') or (AType = 'bool') then
    Result := 'Boolean'
  { Standard typedef vocabulary: these are declared in system headers
    that a file filter normally excludes, so the mapper must know them
    directly.  LP64 assumptions throughout (all Blaise targets). }
  else if (AType = 'size_t') or (AType = 'uintptr_t') or
          (AType = 'uint64_t') or (AType = 'u_int64_t') then
    Result := 'UInt64'
  else if (AType = 'ssize_t') or (AType = 'ptrdiff_t') or
          (AType = 'intptr_t') or (AType = 'int64_t') or
          (AType = 'time_t') or (AType = 'off_t') or (AType = 'clock_t') then
    Result := 'Int64'
  else if (AType = 'int8_t') or (AType = 'uint8_t') or (AType = 'u_char') then
    Result := 'Byte'   { int8_t loses signedness: Blaise has no signed 8-bit }
  else if (AType = 'int16_t') then
    Result := 'SmallInt'
  else if (AType = 'uint16_t') or (AType = 'u_short') then
    Result := 'Word'
  else if (AType = 'int32_t') or (AType = 'pid_t') then
    Result := 'Integer'
  else if (AType = 'uint32_t') or (AType = 'u_int') or
          (AType = 'uid_t') or (AType = 'gid_t') or (AType = 'wchar_t') then
    Result := 'Cardinal'
  else if (AType = 'va_list') or (AType = '__builtin_va_list') or
          (AType = '__gnuc_va_list') then
    Result := 'Pointer';
end;

constructor TPtrAlias.Create(const AName, ATarget: string);
begin
  inherited Create();
  Name := AName;
  Target := ATarget;
end;

constructor TProcTypeDecl.Create(const AName, ADecl: string);
begin
  inherited Create();
  Name := AName;
  Decl := ADecl;
end;

constructor TTypeMapper.Create();
begin
  inherited Create();
  FPtrAliases := TList<TPtrAlias>.Create();
  FPtrSeen := TSet<string>.Create();
  FProcTypes := TList<TProcTypeDecl>.Create();
  FProcBySig := TDictionary<string, string>.Create();
  FProcNames := TSet<string>.Create();
end;

{ Split AArgs ('Display *, int (*)(int, char *), XID') at top-level
  commas, respecting parenthesis depth. }
function SplitTopLevelArgs(const AArgs: string): TList<String>;
var
  I, Depth, Start: Integer;
  B: Integer;
begin
  Result := TList<String>.Create();
  Depth := 0;
  Start := 0;
  for I := 0 to Length(AArgs) - 1 do
  begin
    B := AArgs[I];
    if B = Ord('(') then Depth := Depth + 1
    else if B = Ord(')') then Depth := Depth - 1
    else if (B = Ord(',')) and (Depth = 0) then
    begin
      Result.Add(Trim(MidStr(AArgs, Start, I - Start)));
      Start := I + 1;
    end;
  end;
  if Trim(MidStr(AArgs, Start, Length(AArgs) - Start)) <> '' then
    Result.Add(Trim(MidStr(AArgs, Start, Length(AArgs) - Start)));
end;

function TTypeMapper.FnPtrDecl(const AQualType: string): string;
var
  S, RetC, ArgsC: string;
  StarPos: Integer;
  Ret: string;
  Args: TList<String>;
  I: Integer;
  Params: string;
  Mapped: string;
begin
  Result := '';
  S := Trim(AQualType);
  StarPos := Pos('(*)', S);
  if StarPos < 0 then Exit;
  RetC := Trim(LeftStr(S, StarPos));
  ArgsC := Trim(MidStr(S, StarPos + 3, Length(S)));
  if (ArgsC = '') or (ArgsC[0] <> Ord('(')) or
     (ArgsC[Length(ArgsC) - 1] <> Ord(')')) then Exit;
  ArgsC := Trim(MidStr(ArgsC, 1, Length(ArgsC) - 2));
  if Pos('...', ArgsC) >= 0 then Exit;   { C varargs — unrepresentable }
  Params := '';
  if (ArgsC <> '') and (ArgsC <> 'void') then
  begin
    Args := SplitTopLevelArgs(ArgsC);
    for I := 0 to Args.Count - 1 do
    begin
      Mapped := Self.Map(Args[I]);
      if Mapped = '' then Exit;          { a bare void arg — malformed }
      if I > 0 then Params := Params + '; ';
      Params := Params + 'a' + IntToStr(I) + ': ' + Mapped;
    end;
  end;
  if Params <> '' then
    Params := '(' + Params + ')';
  Ret := Self.Map(RetC);
  if Ret = '' then
    Result := 'procedure' + Params
  else
    Result := 'function' + Params + ': ' + Ret;
end;

function TTypeMapper.MapCallback(const AQualType, AHint: string): string;
var
  Decl: string;
  Name: string;
  N: Integer;
begin
  if Pos('(*)', AQualType) < 0 then
  begin
    Result := Self.Map(AQualType);
    Exit;
  end;
  Decl := Self.FnPtrDecl(AQualType);
  if Decl = '' then
  begin
    Result := 'Pointer';
    Exit;
  end;
  if FProcBySig.ContainsKey(Decl) then
  begin
    FProcBySig.TryGetValue(Decl, Result);
    Exit;
  end;
  Name := 'T' + AHint;
  { A hint collision with a different signature gets a numeric suffix.
    Pascal folds identifier case, so the collision check is
    case-insensitive (same rule as RegisterAlias). }
  N := 1;
  while FProcNames.Contains(UpperCase(Name)) do
  begin
    N := N + 1;
    Name := 'T' + AHint + IntToStr(N);
  end;
  FProcNames.Include(UpperCase(Name));
  FProcBySig.Add(Decl, Name);
  FProcTypes.Add(TProcTypeDecl.Create(Name, Decl));
  Result := Name;
end;

procedure TTypeMapper.RegisterAlias(const AName, ATarget: string);
begin
  { Pascal folds identifier case: PSCREEN and Pscreen are the same
    declaration, so the dedup key must be case-insensitive. }
  if FPtrSeen.Contains(UpperCase(AName)) then Exit;
  FPtrSeen.Include(UpperCase(AName));
  FPtrAliases.Add(TPtrAlias.Create(AName, ATarget));
end;

function TTypeMapper.MapPointer(const APointee: string): string;
var
  Pointee: string;
  Mapped: string;
begin
  Pointee := StripQualifiers(APointee);
  if Pointee = 'char' then
  begin
    Result := 'PChar';
    Exit;
  end;
  if Pointee = 'void' then
  begin
    Result := 'Pointer';
    Exit;
  end;
  Mapped := Self.Map(Pointee);
  { A pointee we cannot name (function type, unparsable construct)
    degrades to an untyped Pointer. }
  if (Mapped = '') or (Pos(' ', Mapped) >= 0) or (Pos('(', Mapped) >= 0) then
  begin
    Result := 'Pointer';
    Exit;
  end;
  Result := 'P' + Mapped;
  RegisterAlias(Result, Mapped);
end;

function TTypeMapper.MapPointerTo(const APointee: string): string;
begin
  Result := Self.MapPointer(APointee);
end;

function TTypeMapper.Map(const AQualType: string): string;
var
  S: string;
  Builtin: string;
  BracketPos: Integer;
  Base: string;
  CountStr: string;
  Count: Integer;
begin
  S := StripQualifiers(AQualType);

  { Function pointers / function types: degrade to Pointer (slice 1). }
  if Pos('(*)', S) >= 0 then
  begin
    Result := 'Pointer';
    Exit;
  end;

  { Pointer: 'T *', 'T **', 'char *const' (trailing const stripped above). }
  if EndsStr('*', S) then
  begin
    Result := MapPointer(Trim(LeftStr(S, Length(S) - 1)));
    Exit;
  end;

  { Fixed-size array: 'int[4]' or 'int [4]'. }
  BracketPos := Pos('[', S);
  if (BracketPos >= 0) and EndsStr(']', S) then
  begin
    Base := Trim(LeftStr(S, BracketPos));
    CountStr := Trim(MidStr(S, BracketPos + 1, Length(S) - BracketPos - 2));
    Count := StrToIntDef(CountStr, 0);
    if Count > 0 then
    begin
      Result := 'array[0..' + IntToStr(Count - 1) + '] of ' + Self.Map(Base);
      Exit;
    end;
    { Incomplete array 'int[]' — decay to pointer. }
    Result := MapPointer(Base);
    Exit;
  end;

  Builtin := MapBuiltin(S);
  if Builtin <> '' then
  begin
    Result := Builtin;
    Exit;
  end;
  if S = 'void' then
  begin
    Result := '';
    Exit;
  end;

  { Anything else is a named type (typedef, struct tag, enum tag) that
    the generated unit will declare — pass the name through. }
  Result := S;
end;

end.
