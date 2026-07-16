{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1002: MaxFunctionLines.

  Flags routines whose source span exceeds a configurable line count
  (default 15).  An AST rule: VisitMethodEnter/Exit bracket each routine, and
  the statement line numbers seen in between give the span.  A frame stack
  handles nested routines; each statement updates every enclosing frame, so an
  outer routine's span includes the text of routines nested inside it.

  Config: rules."BL-1002".params.maxLines (Integer). }

unit Guard.Rule.MaxFunctionLines;

interface

implementation

uses
  SysUtils,
  Generics.Collections,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID          = 'BL-1002';
  RULE_NAME        = 'MaxFunctionLines';
  DEFAULT_MAXLINES = 15;

type
  TMaxFunctionLinesRule = class(TAstRuleBase)
  private
    FStartLines: TList<Integer>;   { stack: routine start line per frame }
    FMaxLines:   TList<Integer>;   { stack: max line seen per frame }
  public
    constructor Create;
    procedure VisitMethodEnter(AMethod: TMethodDecl); override;
    procedure VisitMethodExit(AMethod: TMethodDecl); override;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

constructor TMaxFunctionLinesRule.Create;
begin
  inherited Create();
  FId         := RULE_ID;
  FName       := RULE_NAME;
  FSeverity   := sevWarning;
  FStartLines := TList<Integer>.Create();
  FMaxLines   := TList<Integer>.Create();
end;

procedure TMaxFunctionLinesRule.VisitMethodEnter(AMethod: TMethodDecl);
begin
  FStartLines.Add(AMethod.Line);
  FMaxLines.Add(AMethod.Line);
end;

procedure TMaxFunctionLinesRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  I: Integer;
begin
  { Extend every open frame, so nested-routine lines count toward the span of
    the routines that enclose them. }
  for I := 0 to FMaxLines.Count - 1 do
    if AStmt.Line > FMaxLines[I] then
      FMaxLines[I] := AStmt.Line;
end;

procedure TMaxFunctionLinesRule.VisitMethodExit(AMethod: TMethodDecl);
var
  Top:      Integer;
  StartLn:  Integer;
  MaxLn:    Integer;
  Span:     Integer;
  MaxLines: Integer;
begin
  Top := FMaxLines.Count - 1;
  if Top < 0 then
    Exit;
  StartLn := FStartLines[Top];
  MaxLn   := FMaxLines[Top];
  FStartLines.Delete(Top);
  FMaxLines.Delete(Top);

  MaxLines := FCtx.RuleCfg.GetInt('maxLines', DEFAULT_MAXLINES);
  Span     := MaxLn - StartLn + 1;
  if Span > MaxLines then
    Emit(
      'Routine spans ' + IntToStr(Span) +
      ' lines, exceeding the maximum of ' + IntToStr(MaxLines),
      SourceLoc(FCtx.Model.FileName, AMethod.Line, AMethod.Col));
end;

initialization
  RegisterRule(TMaxFunctionLinesRule.Create());

end.
