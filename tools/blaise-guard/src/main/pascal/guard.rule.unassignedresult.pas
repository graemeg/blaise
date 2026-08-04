{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1006: UnassignedResult.

  A function whose body NEVER assigns Result and never uses Exit(value) returns
  whatever its result slot happens to hold.  Blaise zero-initialises, so this
  does not read stack garbage -- but a function silently returning 0/nil/'' is
  a bug that presents as wrong data far from its cause, and the compiler emits
  no diagnostic.

  Scope: deliberately the UNAMBIGUOUS case only -- not one assignment anywhere
  in the body.  A path-sensitive "assigned on some paths but not others"
  analysis needs a control-flow graph the linter does not build, and would
  false-positive on any function whose assignment is inside a loop or a case
  the rule cannot prove is total.  Under-reporting is the right trade here: a
  finding from this rule is always real.

  Recognised as assigning the result:
    * Result := ...            (including compound targets like Result.Field)
    * Exit(value)
    * Result passed to ANY call -- SetLength(Result, N), FillChar(Result, ...)
      and every var/out parameter write the result in place.  The rule cannot
      tell a var parameter from a value one without resolved signatures, so it
      treats any appearance of Result as an argument as an assignment.  That
      under-reports (a function that only READS Result in a call is missed),
      which is the safe direction.
  A function that only ever raises is exempt -- it has no normal return path.
  An `asm ... end` body is exempt too: it returns through the ABI register and
  never writes the Pascal Result slot (the RTL's atomics and syscall wrappers
  are all of this shape).

  Config: rules."BL-1006".params.  No parameters. }

unit Guard.Rule.UnassignedResult;

interface

implementation

uses
  SysUtils,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-1006';
  RULE_NAME = 'UnassignedResult';

type
  TUnassignedResultRule = class(TAstRuleBase)
  private
    FDepth:      Integer;   { nesting of routines, so only the outermost reports }
    FInFunction: Boolean;
    FAssigned:   Boolean;   { saw Result := / Exit(v) }
    FRaises:     Boolean;   { saw a raise — no normal return path }
    [Unretained] FFunc: TMethodDecl;
  public
    constructor Create;
    procedure Reset; override;
    procedure VisitMethodEnter(AMethod: TMethodDecl); override;
    procedure VisitMethodExit(AMethod: TMethodDecl); override;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
    procedure VisitExpr(AExpr: TASTExpr); override;
  end;

constructor TUnassignedResultRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TUnassignedResultRule.Reset;
begin
  FDepth      := 0;
  FInFunction := False;
  FAssigned   := False;
  FRaises     := False;
  FFunc       := nil;
end;

procedure TUnassignedResultRule.VisitMethodEnter(AMethod: TMethodDecl);
begin
  FDepth := FDepth + 1;
  { Only track the OUTERMOST routine: a nested routine has its own Result and
    its own body, and the walker reports it on its own entry/exit pair. }
  if FDepth <> 1 then Exit;
  FFunc       := AMethod;
  FInFunction := (AMethod <> nil) and (AMethod.ReturnTypeName <> '') and
                 (AMethod.Body <> nil);
  FAssigned   := False;
  FRaises     := False;
end;

procedure TUnassignedResultRule.VisitMethodExit(AMethod: TMethodDecl);
begin
  if (FDepth = 1) and FInFunction and (not FAssigned) and (not FRaises) and
     (FFunc <> nil) then
    Emit('Function ''' + FFunc.Name + ''' never assigns Result (and never ' +
         'uses Exit(value)) - it always returns the zero value',
         SourceLoc(FCtx.Model.FileName, FFunc.Line, FFunc.Col));
  if FDepth = 1 then
  begin
    FInFunction := False;
    FFunc       := nil;
  end;
  FDepth := FDepth - 1;
end;

procedure TUnassignedResultRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  A:  TAssignment;
  X:  TExitStmt;
  F:  TFieldAssignment;
  SA: TStaticSubscriptAssign;
  PC: TProcCall;
  E:  TASTExpr;
  I:  Integer;
begin
  if not FInFunction then Exit;
  if FAssigned and FRaises then Exit;

  if AStmt is TRaiseStmt then
  begin
    FRaises := True;
    Exit;
  end;

  { An `asm ... end` body returns its value in the ABI return register and
    never touches the Pascal Result slot -- the RTL's atomics and syscall
    wrappers are all written this way.  Treat the routine as assigning. }
  if AStmt is TAsmStmt then
  begin
    FAssigned := True;
    Exit;
  end;

  { Result := ... }
  if AStmt is TAssignment then
  begin
    A := TAssignment(AStmt);
    if SameText(A.Name, 'Result') then
      FAssigned := True;
    Exit;
  end;

  { Result.Field := ... / Result[I] := ... — the record/array forms. }
  if AStmt is TFieldAssignment then
  begin
    F := TFieldAssignment(AStmt);
    if SameText(F.RecordName, 'Result') then
      FAssigned := True;
    Exit;
  end;

  { Result[I] := ... — the array-element form. }
  if AStmt is TStaticSubscriptAssign then
  begin
    SA := TStaticSubscriptAssign(AStmt);
    if SameText(SA.ArrayName, 'Result') then
      FAssigned := True;
    Exit;
  end;

  { A procedure CALL taking Result as an argument: SetLength(Result, N) and
    friends write it through a var parameter.  This is a STATEMENT node
    (TProcCall), not an expression, so VisitExpr never sees it. }
  if AStmt is TProcCall then
  begin
    PC := TProcCall(AStmt);
    if PC.Args <> nil then
      for I := 0 to PC.Args.Count - 1 do
      begin
        E := TASTExpr(PC.Args.Items[I]);
        if (E is TIdentExpr) and SameText(TIdentExpr(E).Name, 'Result') then
        begin
          FAssigned := True;
          break;
        end;
      end;
    Exit;
  end;

  { Exit(value) — the shorthand result assignment. }
  if AStmt is TExitStmt then
  begin
    X := TExitStmt(AStmt);
    if X.Value <> nil then
      FAssigned := True;
  end;
end;

{ Result appearing anywhere as a call argument counts as an assignment: a var
  or out parameter writes it in place (SetLength(Result, N) is the common one).
  Without resolved signatures the rule cannot tell var from value, so it errs
  toward silence. }
procedure TUnassignedResultRule.VisitExpr(AExpr: TASTExpr);
var
  FC: TFuncCallExpr;
  MC: TMethodCallExpr;
  I:  Integer;

  procedure ScanArgs(AArgs: TObjectList);
  var
    J: Integer;
    A: TASTExpr;
  begin
    if AArgs = nil then Exit;
    for J := 0 to AArgs.Count - 1 do
    begin
      A := TASTExpr(AArgs.Items[J]);
      if (A is TIdentExpr) and SameText(TIdentExpr(A).Name, 'Result') then
        FAssigned := True;
    end;
  end;

begin
  if not FInFunction then Exit;
  if FAssigned then Exit;
  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    ScanArgs(FC.Args);
    Exit;
  end;
  if AExpr is TMethodCallExpr then
  begin
    MC := TMethodCallExpr(AExpr);
    ScanArgs(MC.Args);
  end;
end;

initialization
  RegisterRule(TUnassignedResultRule.Create());

end.
