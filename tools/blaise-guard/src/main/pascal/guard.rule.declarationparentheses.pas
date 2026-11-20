{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1007: DeclarationParentheses.

  An opt-in house-style rule for projects that want every routine heading to
  carry a parameter list, so a parameterless declaration reads like its call:
  `procedure Foo();` rather than `procedure Foo;`.

  The language accepts both spellings.  Mandatory parentheses on CALLS resolve
  a genuine ambiguity (a bare name could be a variable, a constant or a call);
  a declaration has no such ambiguity, because the procedure/function keyword
  already states what it is.  The choice is therefore purely stylistic, and
  the rule ships DISABLED: a project enables it in its blaise-guard.json.  The
  Blaise project itself does not use it.  See docs/language-rationale.adoc,
  "Parentheses in routine declarations" (GH #192).

  A token rule at INFO severity: a procedure/function/constructor/destructor
  keyword followed by a routine NAME (optionally qualified, TC.Foo, and
  optionally generic, Make<T> or TList<T>.Add) whose next token is not '('.
  A keyword followed directly by ';', ':', 'of', 'begin' or '(' is a
  procedural type or an anonymous method, not a heading, and is skipped.

  The finding sits on the routine's own name (Foo in TC.Foo) with Name() as
  the quick-fix.  A routine with its own type-parameter list gets a fix with
  no replacement text: the () belongs after the '>', not after the name. }

unit Guard.Rule.DeclarationParentheses;

interface

implementation

uses
  SysUtils,
  Generics.Collections,
  uLexer,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-1007';
  RULE_NAME = 'DeclarationParentheses';

type
  TDeclarationParenthesesRule = class(TTokenRuleBase)
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); override;
  public
    constructor Create;
  end;

constructor TDeclarationParenthesesRule.Create;
begin
  inherited Create();
  FId := RULE_ID;
  FName := RULE_NAME;
  FSeverity := sevInfo;
end;

function IsRoutineKeyword(AKind: TTokenKind): Boolean;
begin
  Result := AKind in [tkProcedure, tkFunction, tkConstructor, tkDestructor];
end;

{ Index of the token after the '<' ... '>' list that starts at AIndex,
  honouring nesting; ATokens.Count when the list is unterminated. }
function SkipTypeParams(ATokens: TList<TToken>; AIndex: Int): Int;
var
  Depth: Int;
begin
  Depth := 0;
  for Result := AIndex to ATokens.Count - 1 do
  begin
    if ATokens[Result].Kind = tkLessThan then
      Inc(Depth)
    else if ATokens[Result].Kind = tkGreaterThan then
      Dec(Depth);
    if Depth = 0 then
      Exit(Result + 1);
  end;
  Result := ATokens.Count;
end;

{ Walk the routine name that starts at AIndex -- Foo, TC.Foo, Make<T>,
  TList<T>.Add -- and return the index of the token after it.  ANameIdx is
  the routine's own name; AGeneric is True when the routine itself (not its
  class) has a type-parameter list. }
function ScanRoutineName(ATokens: TList<TToken>; AIndex: Int;
  out ANameIdx: Int; out AGeneric: Boolean): Int;
begin
  ANameIdx := AIndex;
  AGeneric := False;
  Result := AIndex + 1;
  while Result < ATokens.Count do
  begin
    if ATokens[Result].Kind = tkLessThan then
    begin
      Result := SkipTypeParams(ATokens, Result);
      AGeneric := True;
    end
    else if (ATokens[Result].Kind = tkDot) and
            (Result + 1 < ATokens.Count) and
            (ATokens[Result + 1].Kind = tkIdent) then
    begin
      { the type parameters seen so far were the class's }
      ANameIdx := Result + 1;
      AGeneric := False;
      Result := Result + 2;
    end
    else
      Exit;
  end;
end;

procedure TDeclarationParenthesesRule.CheckTokens(AContext: TRuleContext;
  ATokens: TList<TToken>);
var
  I:       Int;
  Next:    Int;
  NameIdx: Int;
  Generic: Boolean;
  Name:    string;
  Fix:     TQuickFix;
begin
  for I := 0 to ATokens.Count - 2 do
  begin
    { a keyword not followed by a name is a procedural type or an
      anonymous method }
    if not IsRoutineKeyword(ATokens[I].Kind) or
       (ATokens[I + 1].Kind <> tkIdent) then
      Continue;
    Next := ScanRoutineName(ATokens, I + 1, NameIdx, Generic);
    if (Next < ATokens.Count) and (ATokens[Next].Kind = tkLParen) then
      Continue;
    Name := ATokens[NameIdx].Value;
    if Generic then
      Fix := TQuickFix.Create('Add () after the type-parameter list')
    else
      Fix := TQuickFix.Create('Add ()', Name + '()');
    AContext.Emit('Routine ''' + Name + ''' is declared without a ' +
      'parameter list: write ' + Name + '()',
      SourceLoc(AContext.Model.FileName, ATokens[NameIdx].Line,
        ATokens[NameIdx].Col), Fix);
  end;
end;

initialization
  RegisterRule(TDeclarationParenthesesRule.Create());

end.
