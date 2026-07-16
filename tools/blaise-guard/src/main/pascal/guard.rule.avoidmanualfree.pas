{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2001: AvoidManualFree.

  Blaise classes are ARC-managed, so an explicit `X.Free` (or `X.Destroy`) is
  usually redundant: objects are released at scope exit or on nil-assignment,
  and reference cycles are broken with [Weak] rather than manual teardown.
  This rule flags such calls so a legacy free can be reconsidered.

  An AST rule: a manual free is a method-call statement whose method name is
  Free/Destroy (TMethodCallStmt).

  Config: rules."BL-2001".params.includeDestroy (Boolean, default true). }

unit Guard.Rule.AvoidManualFree;

interface

implementation

uses
  SysUtils,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2001';
  RULE_NAME = 'AvoidManualFree';

type
  TAvoidManualFreeRule = class(TAstRuleBase)
  public
    constructor Create;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

constructor TAvoidManualFreeRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TAvoidManualFreeRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  Call:           TMethodCallStmt;
  IncludeDestroy: Boolean;
  IsFree:         Boolean;
  Receiver:       string;
begin
  if not (AStmt is TMethodCallStmt) then
    Exit;
  Call := TMethodCallStmt(AStmt);

  IncludeDestroy := FCtx.RuleCfg.GetBool('includeDestroy', True);
  IsFree := SameText(Call.Name, 'Free') or
            (IncludeDestroy and SameText(Call.Name, 'Destroy'));
  if not IsFree then
    Exit;

  if Call.ObjectName <> '' then
    Receiver := Call.ObjectName
  else
    Receiver := '<expr>';

  Emit(
    'Manual ' + Receiver + '.' + Call.Name + ' is usually unnecessary under ' +
    'ARC; rely on scope exit or nil-assignment, and use [Weak] to break cycles',
    SourceLoc(FCtx.Model.FileName, AStmt.Line, AStmt.Col));
end;

initialization
  RegisterRule(TAvoidManualFreeRule.Create());

end.
