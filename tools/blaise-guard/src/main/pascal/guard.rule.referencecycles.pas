{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-2002: ReferenceCycles.

  Under ARC a chain of classes that reference each other strongly (no [Weak] or
  [Unretained] on any edge) is a memory leak: the cycle keeps its own refcounts
  above zero forever.  This rule builds a directed graph of strong class-to-
  class field references across the whole codebase and reports cycles in it.

  A cross-file rule (uses the Reset/Analyse/Finalize lifecycle): VisitClass
  records each class and its strong edges during the per-file pass; Finalize
  runs the cycle detection once the whole graph is known.

  Because BlaiseGuard does not run semantic analysis, field [Weak]/[Unretained]
  is read from the parser's raw attribute list (TFieldDecl.Attributes), not the
  semantic IsWeak flag.  Edges are only drawn between classes actually declared
  somewhere, so unresolved type names never create phantom cycles.  This is a
  static type-graph heuristic (not instance analysis), so self-references are
  excluded by default.

  Config:
    rules."BL-2002".params.includeSelfReference  count a class that strongly
                                                 references its own type
                                                 (default false). }

unit Guard.Rule.ReferenceCycles;

interface

implementation

uses
  SysUtils,
  Generics.Collections,
  uAST,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID   = 'BL-2002';
  RULE_NAME = 'ReferenceCycles';

type
  { A class node in the strong-reference graph. }
  TClassNode = class
  public
    Name:     string;
    FileName: string;
    Line:     Integer;
    Col:      Integer;
    Edges:    TList<string>;   { raw referenced type identifiers (strong only) }
    Color:    Integer;         { DFS: 0 white, 1 gray (on stack), 2 done }
    constructor Create(const AName, AFileName: string; ALine, ACol: Integer);
  end;

  TReferenceCyclesRule = class(TAstRuleBase)
  private
    FNodes:       TDictionary<string, TClassNode>;
    FOrder:       TList<string>;   { declaration order, for deterministic DFS }
    FStack:       TList<string>;   { current DFS path }
    FSeen:        TList<string>;   { canonical keys of already-reported cycles }
    FIncludeSelf: Boolean;
    function  IsWeakField(AField: TFieldDecl): Boolean;
    procedure ExtractIdents(const ATypeName: string; ATarget: TList<string>);
    procedure DetectFrom(const AName: string);
    procedure RecordCycle(AClosingIdx: Integer);
  public
    constructor Create;
    procedure Reset; override;
    procedure VisitClass(AClass: TClassTypeDef; ADecl: TTypeDecl); override;
    procedure Finalize(AContext: TRuleContext); override;
  end;

{ ---- byte-class helpers for identifier scanning ---- }

function IsIdentStart(B: Byte): Boolean;
begin
  Result := ((B >= 65) and (B <= 90)) or   { A-Z }
            ((B >= 97) and (B <= 122)) or   { a-z }
            (B = 95);                        { _ }
end;

function IsIdentCont(B: Byte): Boolean;
begin
  Result := IsIdentStart(B) or ((B >= 48) and (B <= 57));   { + 0-9 }
end;

{ ---- TClassNode ---- }

constructor TClassNode.Create(const AName, AFileName: string;
  ALine, ACol: Integer);
begin
  inherited Create();
  Name     := AName;
  FileName := AFileName;
  Line     := ALine;
  Col      := ACol;
  Edges    := TList<string>.Create();
  Color    := 0;
end;

{ ---- rule ---- }

constructor TReferenceCyclesRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
  FNodes    := TDictionary<string, TClassNode>.Create();
  FOrder    := TList<string>.Create();
end;

procedure TReferenceCyclesRule.Reset;
begin
  FNodes := TDictionary<string, TClassNode>.Create();
  FOrder := TList<string>.Create();
end;

function TReferenceCyclesRule.IsWeakField(AField: TFieldDecl): Boolean;
var
  I: Integer;
  A: string;
begin
  Result := False;
  if AField.Attributes = nil then
    Exit;
  for I := 0 to AField.Attributes.Count - 1 do
  begin
    A := AField.Attributes[I];
    if SameText(A, 'Weak') or SameText(A, 'WeakAttribute') or
       SameText(A, 'Unretained') or SameText(A, 'UnretainedAttribute') then
      Exit(True);
  end;
end;

procedure TReferenceCyclesRule.ExtractIdents(const ATypeName: string;
  ATarget: TList<string>);
var
  I, N:  Integer;
  Ident: string;
begin
  N := Length(ATypeName);
  I := 0;
  while I < N do
  begin
    if IsIdentStart(Byte(ATypeName[I])) then
    begin
      Ident := '';
      while (I < N) and IsIdentCont(Byte(ATypeName[I])) do
      begin
        Ident := Ident + Chr(Byte(ATypeName[I]));
        Inc(I);
      end;
      ATarget.Add(Ident);
    end
    else
      Inc(I);
  end;
end;

procedure TReferenceCyclesRule.VisitClass(AClass: TClassTypeDef;
  ADecl: TTypeDecl);
var
  Node: TClassNode;
  I:    Integer;
  Fld:  TFieldDecl;
  Tn:   string;
begin
  if AClass.IsForward then
    Exit;
  if ADecl.Name = '' then
    Exit;

  if not FNodes.TryGetValue(ADecl.Name, Node) then
  begin
    Node := TClassNode.Create(ADecl.Name, FCtx.Model.FileName,
                              ADecl.Line, ADecl.Col);
    FNodes.Add(ADecl.Name, Node);
    FOrder.Add(ADecl.Name);
  end;

  if AClass.Fields = nil then
    Exit;
  for I := 0 to AClass.Fields.Count - 1 do
  begin
    Fld := TFieldDecl(AClass.Fields[I]);
    if IsWeakField(Fld) then
      Continue;                       { weak/unretained: not a strong edge }
    Tn := Fld.TypeName;
    if (Length(Tn) > 0) and (Byte(Tn[0]) = 94) then
      Continue;                       { '^T': a raw pointer, not an ARC edge }
    ExtractIdents(Tn, Node.Edges);
  end;
end;

procedure TReferenceCyclesRule.RecordCycle(AClosingIdx: Integer);
var
  Members: TList<string>;
  I, MinI: Integer;
  Key:     string;
  Path:    string;
  Anchor:  TClassNode;
begin
  Members := TList<string>.Create();
  for I := AClosingIdx to FStack.Count - 1 do
    Members.Add(FStack[I]);

  { Canonical key = members rotated to start at the smallest name, so the same
    cycle found from a different entry point is reported only once. }
  MinI := 0;
  for I := 1 to Members.Count - 1 do
    if Members[I] < Members[MinI] then
      MinI := I;
  Key := '';
  for I := 0 to Members.Count - 1 do
    Key := Key + Members[(MinI + I) mod Members.Count] + '>';
  if FSeen.IndexOf(Key) >= 0 then
    Exit;
  FSeen.Add(Key);

  Path := '';
  for I := 0 to Members.Count - 1 do
    Path := Path + Members[I] + ' -> ';
  Path := Path + Members[0];   { close the loop back to the start }

  if FNodes.TryGetValue(Members[0], Anchor) then
    Emit(
      'Reference cycle with no [Weak]/[Unretained] edge: ' + Path +
      ' - break it with [Weak] on one reference',
      SourceLoc(Anchor.FileName, Anchor.Line, Anchor.Col));
end;

procedure TReferenceCyclesRule.DetectFrom(const AName: string);
var
  Node, TNode: TClassNode;
  I:     Integer;
  Edge:  string;
begin
  if not FNodes.TryGetValue(AName, Node) then
    Exit;
  Node.Color := 1;
  FStack.Add(AName);

  for I := 0 to Node.Edges.Count - 1 do
  begin
    Edge := Node.Edges[I];
    if (not FIncludeSelf) and (Edge = AName) then
      Continue;
    if FNodes.TryGetValue(Edge, TNode) then
    begin
      if TNode.Color = 0 then
        DetectFrom(Edge)
      else if TNode.Color = 1 then
        RecordCycle(FStack.IndexOf(Edge));
    end;
  end;

  Node.Color := 2;
  FStack.Delete(FStack.Count - 1);
end;

procedure TReferenceCyclesRule.Finalize(AContext: TRuleContext);
var
  I:    Integer;
  Node: TClassNode;
begin
  FIncludeSelf := AContext.RuleCfg.GetBool('includeSelfReference', False);
  FStack := TList<string>.Create();
  FSeen  := TList<string>.Create();

  { Fresh colours before the traversal. }
  for I := 0 to FOrder.Count - 1 do
    if FNodes.TryGetValue(FOrder[I], Node) then
      Node.Color := 0;

  { Reuse the AST-rule emit helper by pointing FCtx at the finalize context. }
  FCtx := AContext;
  try
    for I := 0 to FOrder.Count - 1 do
      if FNodes.TryGetValue(FOrder[I], Node) and (Node.Color = 0) then
        DetectFrom(FOrder[I]);
  finally
    FCtx := nil;
  end;
end;

initialization
  RegisterRule(TReferenceCyclesRule.Create());

end.
