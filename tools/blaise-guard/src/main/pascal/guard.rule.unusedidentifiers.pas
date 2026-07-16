{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1004: UnusedIdentifiers.

  Flags local variables (and, optionally, parameters) declared in a routine but
  never referenced.  An AST rule driven by the walker's scope events:

    VisitMethodEnter  push a scope frame; record parameters
    VisitVarDecl      record locals of the current routine
    VisitStmtEnter    record block-scoped var decls; mark statement-level uses
    VisitExpr         mark expression-level identifier uses
    VisitMethodExit   pop the frame; report declared-but-unused names

  Correctness bias: uses are collected broadly (every identifier that appears
  anywhere as an expression or a statement name field) and marked in ALL open
  frames.  So the only failure mode is UNDER-reporting (a used name that also
  shadows an outer one keeps the outer "used") - never a false "unused".
  Identifier matching is case-insensitive, matching Pascal.

  Because closures and shadowing still make this heuristic, it ships disabled
  by default; enable it deliberately.

  Config:
    rules."BL-1004".enabled          off by default
    rules."BL-1004".params.checkParameters  also report unused parameters
                                             (default false; overrides/interface
                                             conformance make these noisy). }

unit Guard.Rule.UnusedIdentifiers;

interface

implementation

uses
  SysUtils,
  Contnrs,
  Generics.Collections,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-1004';
  RULE_NAME = 'UnusedIdentifiers';

type
  TDeclInfo = class
  public
    Name:    string;    { original spelling, for the message }
    Key:     string;    { lower-cased, for matching }
    Line:    Integer;
    Col:     Integer;
    IsParam: Boolean;
    constructor Create(const AName: string; ALine, ACol: Integer; AIsParam: Boolean);
  end;

  TScopeFrame = class
  public
    Declared: TList<TDeclInfo>;
    Used:     TList<string>;    { lower-cased names seen used }
    constructor Create;
  end;

  TUnusedIdentifiersRule = class(TAstRuleBase)
  private
    FStack:       TList<TScopeFrame>;
    FCheckParams: Boolean;
    procedure MarkUsed(const AName: string);
    procedure DeclareInTop(const AName: string; ALine, ACol: Integer;
                           AIsParam: Boolean);
  public
    constructor Create;
    procedure Reset; override;
    procedure VisitMethodEnter(AMethod: TMethodDecl); override;
    procedure VisitMethodExit(AMethod: TMethodDecl); override;
    procedure VisitVarDecl(AVar: TVarDecl); override;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
    procedure VisitExpr(AExpr: TASTExpr); override;
  end;

{ ---- helpers ---- }

constructor TDeclInfo.Create(const AName: string; ALine, ACol: Integer;
  AIsParam: Boolean);
begin
  inherited Create();
  Name    := AName;
  Key     := LowerCase(AName);
  Line    := ALine;
  Col     := ACol;
  IsParam := AIsParam;
end;

constructor TScopeFrame.Create;
begin
  inherited Create();
  Declared := TList<TDeclInfo>.Create();
  Used     := TList<string>.Create();
end;

{ ---- rule ---- }

constructor TUnusedIdentifiersRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
  FStack    := TList<TScopeFrame>.Create();
end;

procedure TUnusedIdentifiersRule.Reset;
begin
  FStack := TList<TScopeFrame>.Create();
end;

procedure TUnusedIdentifiersRule.MarkUsed(const AName: string);
var
  Key: string;
  I:   Integer;
begin
  if AName = '' then
    Exit;
  Key := LowerCase(AName);
  { Mark in every open frame - a use in an inner scope conservatively keeps an
    outer same-named variable "used" too. }
  for I := 0 to FStack.Count - 1 do
    if FStack[I].Used.IndexOf(Key) < 0 then
      FStack[I].Used.Add(Key);
end;

procedure TUnusedIdentifiersRule.DeclareInTop(const AName: string;
  ALine, ACol: Integer; AIsParam: Boolean);
begin
  if (AName = '') or (FStack.Count = 0) then
    Exit;   { no enclosing routine -> a global/top-level name we don't track }
  FStack[FStack.Count - 1].Declared.Add(
    TDeclInfo.Create(AName, ALine, ACol, AIsParam));
end;

procedure TUnusedIdentifiersRule.VisitMethodEnter(AMethod: TMethodDecl);
var
  Frame: TScopeFrame;
  I:     Integer;
  P:     TMethodParam;
begin
  FCheckParams := FCtx.RuleCfg.GetBool('checkParameters', False);
  Frame := TScopeFrame.Create();
  FStack.Add(Frame);
  if AMethod.Params <> nil then
    for I := 0 to AMethod.Params.Count - 1 do
    begin
      P := TMethodParam(AMethod.Params[I]);
      DeclareInTop(P.ParamName, P.Line, P.Col, True);
    end;
end;

procedure TUnusedIdentifiersRule.VisitVarDecl(AVar: TVarDecl);
var
  I: Integer;
begin
  if AVar.Names = nil then
    Exit;
  for I := 0 to AVar.Names.Count - 1 do
    DeclareInTop(AVar.Names[I], AVar.Line, AVar.Col, False);
end;

procedure TUnusedIdentifiersRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  VD: TVarDecl;
  I:  Integer;
begin
  { Block-scoped var statement declares locals in the current routine. }
  if AStmt is TVarDeclStmt then
  begin
    VD := TVarDeclStmt(AStmt).Decl;
    if (VD <> nil) and (VD.Names <> nil) then
      for I := 0 to VD.Names.Count - 1 do
        DeclareInTop(VD.Names[I], VD.Line, VD.Col, False);
  end

  { Statement-level name fields count as uses of the named variable. }
  else if AStmt is TAssignment then
    MarkUsed(TAssignment(AStmt).Name)
  else if AStmt is TFieldAssignment then
    MarkUsed(TFieldAssignment(AStmt).RecordName)
  else if AStmt is TStaticSubscriptAssign then
    MarkUsed(TStaticSubscriptAssign(AStmt).ArrayName)
  else if AStmt is TMethodCallStmt then
    MarkUsed(TMethodCallStmt(AStmt).ObjectName)
  else if AStmt is TProcCall then
    MarkUsed(TProcCall(AStmt).Name)
  else if AStmt is TForStmt then
    MarkUsed(TForStmt(AStmt).VarName)
  else if AStmt is TForInStmt then
    MarkUsed(TForInStmt(AStmt).VarName);
end;

procedure TUnusedIdentifiersRule.VisitExpr(AExpr: TASTExpr);
begin
  if AExpr is TIdentExpr then
    MarkUsed(TIdentExpr(AExpr).Name)
  else if AExpr is TFieldAccessExpr then
    MarkUsed(TFieldAccessExpr(AExpr).RecordName)   { leaf receiver (Base = nil) }
  else if AExpr is TFuncCallExpr then
    MarkUsed(TFuncCallExpr(AExpr).Name)
  else if AExpr is TMethodCallExpr then
    MarkUsed(TMethodCallExpr(AExpr).ObjectName)
  else if AExpr is TSupportsExpr then
    MarkUsed(TSupportsExpr(AExpr).OutVarName);
end;

procedure TUnusedIdentifiersRule.VisitMethodExit(AMethod: TMethodDecl);
var
  Frame: TScopeFrame;
  I:     Integer;
  D:     TDeclInfo;
  Kind:  string;
begin
  if FStack.Count = 0 then
    Exit;
  Frame := FStack[FStack.Count - 1];
  FStack.Delete(FStack.Count - 1);

  for I := 0 to Frame.Declared.Count - 1 do
  begin
    D := Frame.Declared[I];
    if D.IsParam and (not FCheckParams) then
      Continue;
    if Frame.Used.IndexOf(D.Key) >= 0 then
      Continue;

    if D.IsParam then
      Kind := 'parameter'
    else
      Kind := 'local variable';
    Emit(
      'Unused ' + Kind + ' ''' + D.Name + '''',
      SourceLoc(FCtx.Model.FileName, D.Line, D.Col));
  end;
end;

initialization
  RegisterRule(TUnusedIdentifiersRule.Create());

end.
