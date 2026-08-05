{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2003: StringIndexing.

  Blaise strings and arrays are 0-based: the first element is [0].  A literal
  subscript of 1 (`ident[1]`) is a common symptom of a 1-based indexing
  assumption carried over from Delphi/FPC, where the first character is [1].
  This rule flags that pattern for review.

  It is a heuristic, so it reports at INFO severity and is a token rule (no AST
  needed): it scans for the token window  IDENT '[' INTLIT(1) ']'.

  Config: rules."BL-2003".params.enabled etc. handled by the engine. }

unit Guard.Rule.StringIndexing;

interface

implementation

uses
  Generics.Collections,
  uLexer,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2003';
  RULE_NAME = 'StringIndexing';

type
  TStringIndexingRule = class(TTokenRuleBase)
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); override;
  public
    constructor Create;
  end;

constructor TStringIndexingRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevInfo;
end;

{ A name that plainly denotes a COLLECTION, where [1] means "the second
  element" and is perfectly correct.  Without resolved types the rule cannot
  tell a string from a list, so this is the discriminator: measured against
  compiler/src/main/pascal, 427 of 543 hits were plural names (Items, Stmts,
  TypeDecls, Methods, Strings...) and every one inspected was a legitimate
  element access.  Anything ending in 's' is therefore assumed a collection. }
function LooksLikeCollection(const AName: string): Boolean;
var
  N: string;
begin
  N := LowerCase(AName);
  Result := (Length(N) > 1) and (N[Length(N) - 1] = StrAt('s', 0));
end;

procedure TStringIndexingRule.CheckTokens(AContext: TRuleContext;
  ATokens: TList<TToken>);
var
  I: Integer;
begin
  { Window: IDENT '[' 1 ']'.  Stop 3 before the end so the window fits. }
  for I := 0 to ATokens.Count - 4 do
    if (ATokens[I].Kind = tkIdent) and
       (ATokens[I + 1].Kind = tkLBracket) and
       (ATokens[I + 2].Kind = tkIntLit) and (ATokens[I + 2].Value = '1') and
       (ATokens[I + 3].Kind = tkRBracket) and
       (not LooksLikeCollection(ATokens[I].Value)) then
      AContext.Emit(
        'Subscript literal 1 on ''' + ATokens[I].Value +
        ''': Blaise indexing is 0-based (first element is [0]) - verify this ' +
        'is not a 1-based assumption',
        SourceLoc(AContext.Model.FileName,
                  ATokens[I + 2].Line, ATokens[I + 2].Col));
end;

initialization
  RegisterRule(TStringIndexingRule.Create());

end.
