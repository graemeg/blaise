{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2006: ClassicTypeNames.

  Blaise's type names state their width: Int8 .. Int64, UInt8 .. UInt64,
  Float32 / Float64, and the pointer-sized Int / UInt.  The classic FPC /
  Delphi names (Integer, Cardinal, Double, LongInt, Extended, ...) are being
  retired: some are builtins today, the rest come from the opt-in
  ClassicPascalTypes unit, and all of them move to that unit once the
  builtins go (docs/type-standardisation-design.adoc).  This rule reports each
  classic name used as a type, with its replacement as a quick-fix, so code
  can migrate ahead of that.  Byte is not reported: it stays a builtin.

  A token rule at INFO severity: an identifier naming a classic type, unless
  it is a member access (preceded by '.'), or the file declares that name
  itself -- anywhere it is followed by ':' or '=' (a variable called Comp, a
  field called Word, or ClassicPascalTypes' own `Real = Float64`).  Such a
  name is the file's own identifier at every occurrence, not the classic
  type. }

unit Guard.Rule.ClassicTypeNames;

interface

implementation

uses
  SysUtils,
  Generics.Collections,
  uLexer,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2006';
  RULE_NAME = 'ClassicTypeNames';

type
  TClassicTypeNamesRule = class(TTokenRuleBase)
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); override;
  public
    constructor Create;
  end;

constructor TClassicTypeNamesRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevInfo;
end;

{ The replacement for classic type name AName, and an optional note that
  qualifies it; False when AName is not a classic type name. }
function ClassicReplacement(const AName: string; out AReplacement,
  ANote: string): Boolean;
var
  N: string;
begin
  Result := True;
  ANote := '';
  N := LowerCase(AName);
  if N = 'integer' then
  begin
    AReplacement := 'Int32';
    ANote := ' (or Int, the pointer-sized integer, for counts and indices)';
  end
  else if (N = 'longint') then
    AReplacement := 'Int32'
  else if (N = 'cardinal') or (N = 'longword') then
    AReplacement := 'UInt32'
  else if N = 'smallint' then
    AReplacement := 'Int16'
  else if N = 'shortint' then
    AReplacement := 'Int8'
  else if N = 'word' then
    AReplacement := 'UInt16'
  else if (N = 'qword') then
    AReplacement := 'UInt64'
  else if N = 'comp' then
    AReplacement := 'Int64'
  else if (N = 'nativeint') or (N = 'ptrint') then
    AReplacement := 'Int'
  else if (N = 'nativeuint') or (N = 'ptruint') then
    AReplacement := 'UInt'
  else if N = 'single' then
    AReplacement := 'Float32'
  else if (N = 'double') or (N = 'real') then
  begin
    AReplacement := 'Float64';
    ANote := ' (or Float, which is always Float64)';
  end
  else if N = 'extended' then
  begin
    AReplacement := 'Float64';
    ANote := ' - note that Extended was the 80-bit x87 type in FPC on x86; ' +
      'code that relied on 80-bit intermediate precision computes in 64-bit';
  end
  else
    Result := False;
end;

procedure TClassicTypeNamesRule.CheckTokens(AContext: TRuleContext;
  ATokens: TList<TToken>);
var
  I:           Int;
  Replacement: string;
  Note:        string;
  OwnNames:    TSet<string>;
begin
  { First pass: the classic names this file declares as its own identifiers
    (followed by ':' or '=') -- every occurrence of those is the file's own
    variable, field or type.  A name preceded by ':' or 'of' is in a TYPE
    position even when '=' follows (a typed constant `K: Integer = 5`, a
    default parameter `A: Double = 0`, a typed array constant
    `array[0..3] of Double = (...)`), so it is not a declaration of that
    name. }
  OwnNames := TSet<string>.Create();
  for I := 0 to ATokens.Count - 2 do
    if (ATokens[I].Kind = tkIdent) and
       ((ATokens[I + 1].Kind = tkColon) or (ATokens[I + 1].Kind = tkEquals)) and
       ((I = 0) or not (ATokens[I - 1].Kind in [tkColon, tkOf])) and
       ClassicReplacement(ATokens[I].Value, Replacement, Note) then
      OwnNames.Include(LowerCase(ATokens[I].Value));
  for I := 0 to ATokens.Count - 1 do
  begin
    if ATokens[I].Kind <> tkIdent then
      Continue;
    if not ClassicReplacement(ATokens[I].Value, Replacement, Note) then
      Continue;
    if OwnNames.Contains(LowerCase(ATokens[I].Value)) then
      Continue;
    { a member access: R.Word }
    if (I > 0) and (ATokens[I - 1].Kind = tkDot) then
      Continue;
    AContext.Emit(
      'Classic type name ''' + ATokens[I].Value + ''': use ' + Replacement +
      Note,
      SourceLoc(AContext.Model.FileName, ATokens[I].Line, ATokens[I].Col),
      TQuickFix.Create('Replace with ' + Replacement, Replacement));
  end;
end;

initialization
  RegisterRule(TClassicTypeNamesRule.Create());

end.
