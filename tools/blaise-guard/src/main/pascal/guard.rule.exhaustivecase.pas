{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-3002: ExhaustiveCase.

  A `case` over an enumeration that omits members and has no `else` falls
  through silently: adding a member to the enum leaves every existing case
  statement quietly incomplete, with no compile error and no warning.  That is
  the failure mode behind several of this project's own backend bugs -- a new
  variant is handled in one backend's dispatch and forgotten in another's.

  Detection without a semantic pass
  ---------------------------------
  BlaiseGuard parses but does not run uSemantic, so TCaseStmt.Selector has no
  ResolvedType and the selector's enum type cannot be looked up through the
  type system.  Instead the rule collects the enum types declared IN THIS FILE
  (VisitTypeDecl) and matches a case statement to one by its branch LABELS: if
  every label is a member name of exactly one declared enum, that enum is the
  selector type.  Any label that is not a bare identifier (a literal, a range,
  a constant) makes the match ambiguous and the statement is skipped.

  Consequences, deliberately accepted:
    * A case over an enum declared in ANOTHER unit is not checked (single-file
      analysis).  Silent, by design -- reporting it would need the uses chain.
    * Two enums in one file sharing every label used would be ambiguous; the
      rule skips rather than guess.
  Both directions fail SAFE: the rule under-reports, never invents a finding.

  Config: rules."BL-3002".params.  No parameters -- a case is exhaustive or it
  is not. }

unit Guard.Rule.ExhaustiveCase;

interface

implementation

uses
  SysUtils,
  Classes,
  Generics.Collections,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-3002';
  RULE_NAME = 'ExhaustiveCase';

type
  TExhaustiveCaseRule = class(TAstRuleBase)
  private
    { Enum name -> its member names.  Rebuilt per file in Analyse's walk;
      Reset clears it so repeated runs in one process stay independent.
      ORDERED so the members can be walked by index — plain TDictionary
      exposes no key enumeration. }
    FEnums: TOrderedDictionary<string, TStringList>;
    { The enum whose members exactly cover ALabels, or '' when no single
      declared enum matches (unknown type, foreign unit, or ambiguous). }
    function MatchEnum(ALabels: TStringList): string;
    procedure ClearEnums;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Reset; override;
    procedure VisitTypeDecl(ADecl: TTypeDecl); override;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); override;
  end;

constructor TExhaustiveCaseRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
  FEnums    := TOrderedDictionary<string, TStringList>.Create();
end;

destructor TExhaustiveCaseRule.Destroy;
begin
  { ClearEnums frees the member lists AND replaces the map, so the fresh map
    it leaves behind is what gets freed here. }
  Self.ClearEnums();
  FEnums.Free();
  FEnums := nil;
  inherited Destroy();
end;

procedure TExhaustiveCaseRule.ClearEnums;
var
  I: Integer;
  L: TStringList;
begin
  { The dictionary is non-owning over its VALUES, so free the lists first.
    TOrderedDictionary has no Clear, so the map itself is replaced. }
  for I := 0 to FEnums.Count - 1 do
    if FEnums.TryGetValue(FEnums.GetKey(I), L) then
      L.Free();
  FEnums.Free();
  FEnums := TOrderedDictionary<string, TStringList>.Create();
end;

procedure TExhaustiveCaseRule.Reset;
begin
  Self.ClearEnums();
end;

procedure TExhaustiveCaseRule.VisitTypeDecl(ADecl: TTypeDecl);
var
  ED:      TEnumTypeDef;
  Members: TStringList;
  I:       Integer;
begin
  if ADecl = nil then Exit;
  if not (ADecl.Def is TEnumTypeDef) then Exit;
  ED := TEnumTypeDef(ADecl.Def);
  Members := TStringList.Create();
  for I := 0 to ED.Members.Count - 1 do
    Members.Add(LowerCase(ED.Members[I]));
  FEnums.SetItem(LowerCase(ADecl.Name), Members);
end;

function TExhaustiveCaseRule.MatchEnum(ALabels: TStringList): string;
var
  K:       string;
  Members: TStringList;
  I, N:    Integer;
  AllIn:   Boolean;
  Hits:    Integer;
begin
  Result := '';
  Hits   := 0;
  for N := 0 to FEnums.Count - 1 do
  begin
    K := FEnums.GetKey(N);
    if not FEnums.TryGetValue(K, Members) then Continue;
    AllIn := True;
    for I := 0 to ALabels.Count - 1 do
      if Members.IndexOf(ALabels[I]) < 0 then
      begin
        AllIn := False;
        break;
      end;
    if AllIn then
    begin
      Result := K;
      Hits   := Hits + 1;
    end;
  end;
  { Ambiguous — more than one declared enum could be the selector type. }
  if Hits <> 1 then
    Result := '';
end;

procedure TExhaustiveCaseRule.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer);
var
  CS:       TCaseStmt;
  Branch:   TCaseBranch;
  Labels:   TStringList;
  Missing:  TStringList;
  Members:  TStringList;
  EnumName: string;
  I, J:     Integer;
  E:        TASTExpr;
  Bare:     Boolean;
begin
  if not (AStmt is TCaseStmt) then Exit;
  CS := TCaseStmt(AStmt);
  { An else clause makes the statement total by construction. }
  if CS.ElseStmt <> nil then Exit;
  if FEnums.Count = 0 then Exit;

  Labels  := nil;
  Missing := nil;
  try
    Labels := TStringList.Create();
    Bare   := True;
    for I := 0 to CS.Branches.Count - 1 do
    begin
      Branch := TCaseBranch(CS.Branches.Items[I]);
      for J := 0 to Branch.Values.Count - 1 do
      begin
        E := TASTExpr(Branch.Values.Items[J]);
        { Only bare identifiers can be matched against enum members without
          the semantic pass; anything else (literal, range, const) makes the
          selector type indeterminate, so skip the whole statement. }
        if not (E is TIdentExpr) then
        begin
          Bare := False;
          break;
        end;
        Labels.Add(LowerCase(TIdentExpr(E).Name));
      end;
      if not Bare then break;
    end;
    if not Bare then Exit;
    if Labels.Count = 0 then Exit;

    EnumName := Self.MatchEnum(Labels);
    if EnumName = '' then Exit;
    if not FEnums.TryGetValue(EnumName, Members) then Exit;

    Missing := TStringList.Create();
    for I := 0 to Members.Count - 1 do
      if Labels.IndexOf(Members[I]) < 0 then
        Missing.Add(Members[I]);
    if Missing.Count = 0 then Exit;

    Emit(
      'case over enum covers ' + IntToStr(Labels.Count) + ' of ' +
      IntToStr(Members.Count) + ' members and has no else - missing: ' +
      Missing.CommaText +
      ' (adding an enum member will not flag this statement)',
      SourceLoc(FCtx.Model.FileName, CS.Line, CS.Col));
  finally
    Labels.Free();
    Missing.Free();
  end;
end;

initialization
  RegisterRule(TExhaustiveCaseRule.Create());

end.
