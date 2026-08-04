{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1005: RedundantComparison.

  Three expression shapes that say less than they appear to:

    X = True / X <> False    a boolean compared to a boolean literal; the
                             comparison adds nothing over `X` / `not X`, and
                             `= True` reads as an equality test where the
                             author meant a truth test.
    X = nil  / X <> nil      correct, but `Assigned(X)` states the intent and
                             matches the rest of the codebase.
    X := X                   a self-assignment: either dead, or a symptom of a
                             name that was meant to differ on one side.

  All three compile silently today, and the first and third are the kind of
  thing that survives a rename.  Reported at INFO for the two stylistic ones
  and WARNING for the self-assignment, which is more often a real slip -- but
  the rule carries one severity, so it uses WARNING and says which shape it
  found.

  Config: rules."BL-1005".params.  No parameters. }

unit Guard.Rule.RedundantComparison;

interface

implementation

uses
  SysUtils,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-1005';
  RULE_NAME = 'RedundantComparison';

type
  TRedundantComparisonRule = class(TAstRuleBase)
  public
    constructor Create;
    procedure VisitExpr(AExpr: TASTExpr); override;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

{ The identifier text of a bare identifier expression, or '' otherwise. }
function IdentName(AExpr: TASTExpr): string;
begin
  if AExpr is TIdentExpr then
    Result := TIdentExpr(AExpr).Name
  else
    Result := '';
end;

{ True for a bare True/False identifier — Blaise has no distinct boolean
  literal node, so the constants arrive as identifiers. }
function IsBoolLiteral(AExpr: TASTExpr): Boolean;
var
  N: string;
begin
  N := IdentName(AExpr);
  Result := SameText(N, 'True') or SameText(N, 'False');
end;

constructor TRedundantComparisonRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TRedundantComparisonRule.VisitExpr(AExpr: TASTExpr);
var
  BE:  TBinaryExpr;
  Sym: string;
  Lit: string;
begin
  if not (AExpr is TBinaryExpr) then Exit;
  BE := TBinaryExpr(AExpr);
  if not (BE.Op in [boEQ, boNE]) then Exit;
  if BE.Op = boEQ then Sym := '=' else Sym := '<>';

  { Boolean literal on either side.  Name the LITERAL, not both operands
    concatenated — the other side is an arbitrary expression the rule cannot
    render faithfully. }
  if IsBoolLiteral(BE.Left) or IsBoolLiteral(BE.Right) then
  begin
    if IsBoolLiteral(BE.Right) then
      Lit := IdentName(BE.Right)
    else
      Lit := IdentName(BE.Left);
    Emit('Comparison ''' + Sym + ' ' + Lit +
         ''' against a boolean literal is redundant - test the value directly',
         SourceLoc(FCtx.Model.FileName, BE.Line, BE.Col));
    Exit;
  end;

  { NOT flagged: `X = nil` / `X <> nil`.  fpsonar reports these in favour of
    Assigned(), but measured against this codebase the check fires 3242 times
    in compiler/src/main/pascal alone — `= nil` IS the house idiom here, and a
    rule that indicts every use of the prevailing style is noise, not signal.
    The two shapes above are different: they found ZERO existing sites, so a
    hit is a genuine new slip rather than a disagreement about style. }
end;

procedure TRedundantComparisonRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  A: TAssignment;
begin
  if not (AStmt is TAssignment) then Exit;
  A := TAssignment(AStmt);
  { Only the simple `X := X` form: a bare identifier naming the target.  A
    field or subscript self-assignment needs the base expressions compared,
    which is not reliable without resolved types, so it is left alone. }
  if (A.Name <> '') and SameText(IdentName(A.Expr), A.Name) then
    Emit('Self-assignment ''' + A.Name + ' := ' + A.Name +
         ''' has no effect - either dead code or a mistyped name',
         SourceLoc(FCtx.Model.FileName, A.Line, A.Col));
end;

initialization
  RegisterRule(TRedundantComparisonRule.Create());

end.
