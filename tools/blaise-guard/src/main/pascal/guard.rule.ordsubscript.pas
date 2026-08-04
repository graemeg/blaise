{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2004: OrdSubscript.

  Fetch a string byte with StrAt/OrdAt, not Ord(S[I]).

  The bare subscript-then-Ord idiom has been observed to MISCOMPILE under the
  self-hosted native stage: it baked a pointer-sized garbage immediate instead
  of loading the byte.  The symptom is not a compile error but wrong data much
  later, and it only appears once the compiler is compiling itself -- which is
  why it cost real debugging time before the cause was known.  StrAt/OrdAt are
  the stage-stable helpers used throughout the backends.

  This is a house rule for THIS codebase (see CLAUDE.md, "Read a string byte
  with StrAt/OrdAt"), not a general Pascal style preference, so it carries a
  concrete rationale in the message rather than a bare "prefer X".

  Heuristic and token-based: it matches the window  'Ord' '(' IDENT '['  and
  cannot tell a string subscript from an array-of-Byte one, so it reports at
  INFO.  An array subscript inside Ord() is harmless but rare, and reviewing it
  costs little next to missing a miscompile. }

unit Guard.Rule.OrdSubscript;

interface

implementation

uses
  Generics.Collections,
  uLexer,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2004';
  RULE_NAME = 'OrdSubscript';

type
  TOrdSubscriptRule = class(TTokenRuleBase)
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); override;
  public
    constructor Create;
  end;

constructor TOrdSubscriptRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevInfo;
end;

procedure TOrdSubscriptRule.CheckTokens(AContext: TRuleContext;
  ATokens: TList<TToken>);
var
  I: Integer;
begin
  { Window: Ord '(' IDENT '['.  Stop 3 before the end so the window fits. }
  for I := 0 to ATokens.Count - 4 do
    if (ATokens[I].Kind = tkIdent) and
       SameText(ATokens[I].Value, 'Ord') and
       (ATokens[I + 1].Kind = tkLParen) and
       (ATokens[I + 2].Kind = tkIdent) and
       (ATokens[I + 3].Kind = tkLBracket) then
      AContext.Emit(
        'Ord(' + ATokens[I + 2].Value + '[...]) reads a string byte by ' +
        'subscript: use StrAt/OrdAt instead - the bare form has been seen to ' +
        'miscompile under the self-hosted native stage (baking a garbage ' +
        'immediate rather than loading the byte)',
        SourceLoc(AContext.Model.FileName,
                  ATokens[I].Line, ATokens[I].Col));
end;

initialization
  RegisterRule(TOrdSubscriptRule.Create());

end.
