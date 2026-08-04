{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2005: EmptyHandler.

  An `except` block with no statements SWALLOWS the exception: control resumes
  after the try and the failure is gone, with no message, no log and no exit
  code.  A debugging session that starts "it just silently does nothing" often
  ends at one of these.  An empty `finally` is harmless at runtime but is
  either a leftover or an unfinished cleanup path, so it is reported at a lower
  severity.

  Empty typed handlers (`on E: EFoo do ;`) count too -- a deliberate "ignore
  this specific exception" is usually written with a comment explaining why,
  and the rule cannot see comments, so it reports and lets the reader confirm.

  To intentionally ignore an exception, write the reason as a statement the
  compiler keeps -- a log call, or a comment plus an explicit no-op -- rather
  than an empty block.

  Config: rules."BL-2005".params.  No parameters. }

unit Guard.Rule.EmptyHandler;

interface

implementation

uses
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2005';
  RULE_NAME = 'EmptyHandler';

type
  TEmptyHandlerRule = class(TAstRuleBase)
  public
    constructor Create;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

{ True when a compound body carries no statements at all.  A nil body is the
  parser's representation of an absent block, which is equally empty. }
function IsEmptyBody(ABody: TCompoundStmt): Boolean;
begin
  Result := (ABody = nil) or (ABody.Stmts = nil) or (ABody.Stmts.Count = 0);
end;

constructor TEmptyHandlerRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TEmptyHandlerRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  TE: TTryExceptStmt;
  TF: TTryFinallyStmt;
  HC: TExceptHandlerClause;
  I:  Integer;
begin
  if AStmt is TTryFinallyStmt then
  begin
    TF := TTryFinallyStmt(AStmt);
    if IsEmptyBody(TF.FinallyBody) then
      Emit('Empty finally block - either dead code or an unfinished cleanup path',
           SourceLoc(FCtx.Model.FileName, TF.Line, TF.Col));
    Exit;
  end;

  if not (AStmt is TTryExceptStmt) then Exit;
  TE := TTryExceptStmt(AStmt);

  { Plain catch-all `except <nothing> end`: swallows everything. }
  if (TE.Handlers = nil) or (TE.Handlers.Count = 0) then
  begin
    if IsEmptyBody(TE.ExceptBody) then
      Emit('Empty except block silently swallows the exception - handle it, ' +
           'log it, or re-raise with a bare ''raise''',
           SourceLoc(FCtx.Model.FileName, TE.Line, TE.Col));
    Exit;
  end;

  { Typed handlers: report each empty arm at its own location. }
  for I := 0 to TE.Handlers.Count - 1 do
  begin
    HC := TExceptHandlerClause(TE.Handlers.Items[I]);
    if IsEmptyBody(HC.Body) then
      Emit('Empty ''on ' + HC.TypeName + ''' handler silently swallows that ' +
           'exception - handle it, log it, or re-raise with a bare ''raise''',
           SourceLoc(FCtx.Model.FileName, TE.Line, TE.Col));
  end;

  { A catch-all else arm after typed handlers is the same swallow. }
  if (TE.ElseBody <> nil) and IsEmptyBody(TE.ElseBody) then
    Emit('Empty catch-all else arm silently swallows every other exception',
         SourceLoc(FCtx.Model.FileName, TE.Line, TE.Col));
end;

initialization
  RegisterRule(TEmptyHandlerRule.Create());

end.
