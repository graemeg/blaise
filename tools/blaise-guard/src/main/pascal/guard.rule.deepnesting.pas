{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1003: DeepNesting.

  Flags control-flow constructs (if/case/while/for/repeat/try) nested more
  deeply than a configurable threshold (default 3).  An AST rule: it is itself
  an AST visitor, and the walker supplies the nesting depth of each statement.

  To keep the output quiet it reports only the shallowest offending construct
  on each path - the first statement whose depth is exactly threshold+1 - not
  every statement below it.

  Config: rules."BL-1003".params.maxDepth (Integer). }

unit Guard.Rule.DeepNesting;

interface

implementation

uses
  SysUtils,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID         = 'BL-1003';
  RULE_NAME       = 'DeepNesting';
  DEFAULT_MAXDEPTH = 3;

type
  TDeepNestingRule = class(TAstRuleBase)
  public
    constructor Create;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

{ True for the statements that constitute a level of control-flow nesting. }
function IsNestingStmt(AStmt: TASTStmt): Boolean;
begin
  Result :=
    (AStmt is TIfStmt)   or (AStmt is TCaseStmt)  or
    (AStmt is TWhileStmt) or (AStmt is TForStmt)  or
    (AStmt is TForInStmt) or (AStmt is TRepeatStmt) or
    (AStmt is TTryFinallyStmt) or (AStmt is TTryExceptStmt);
end;

constructor TDeepNestingRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TDeepNestingRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  MaxDepth: Integer;
begin
  MaxDepth := FCtx.RuleCfg.GetInt('maxDepth', DEFAULT_MAXDEPTH);
  { Report at the first level that breaks the limit, and only for a genuine
    nesting construct, so a deeply nested block yields one finding not many. }
  if (ADepth = MaxDepth + 1) and IsNestingStmt(AStmt) then
    Emit(
      'Control-flow nesting is ' + IntToStr(ADepth) +
      ' levels deep, exceeding the maximum of ' + IntToStr(MaxDepth),
      SourceLoc(FCtx.Model.FileName, AStmt.Line, AStmt.Col));
end;

initialization
  RegisterRule(TDeepNestingRule.Create());

end.
