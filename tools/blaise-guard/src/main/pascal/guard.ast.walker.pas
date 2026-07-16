{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - AST traversal (the Visitor pattern, externalised).

  The compiler's uAST nodes are plain data classes with no Accept method, so
  the traversal lives here rather than on the nodes.  TAstVisitor is a Null
  Object: every hook is an empty virtual, so a rule overrides only the node
  kinds it cares about and ignores the rest.  TAstWalker knows the shape of the
  tree and drives the hooks in source order, tracking control-flow nesting
  depth for the rules that need it (DeepNesting).

  Depth convention: a statement sitting directly in a routine/block body is at
  depth 1.  Descending into the body of a control-flow construct
  (if/case/while/for/repeat/try) adds one; a bare begin/end compound is
  transparent (it does not add a level), matching how a developer perceives
  nesting. }

unit Guard.Ast.Walker;

interface

uses
  Contnrs,
  uAST;

type
  TAstVisitor = class
  public
    { A type declaration of any kind (alias, enum, record, class, ...). }
    procedure VisitTypeDecl(ADecl: TTypeDecl); virtual;
    { Convenience fan-out: called after VisitTypeDecl when the decl defines a
      class, with the class body already narrowed. }
    procedure VisitClass(AClass: TClassTypeDef; ADecl: TTypeDecl); virtual;
    procedure VisitVarDecl(AVar: TVarDecl); virtual;
    procedure VisitConstDecl(AConst: TConstDecl); virtual;
    { Routine bodies bracket their contents with enter/exit so a rule can push
      and pop per-routine state (line spans, local-scope tables). }
    procedure VisitMethodEnter(AMethod: TMethodDecl); virtual;
    procedure VisitMethodExit(AMethod: TMethodDecl); virtual;
    procedure VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); virtual;
    procedure VisitStmtExit(AStmt: TASTStmt; ADepth: Integer); virtual;
  end;

  TAstWalker = class
  private
    [Unretained] FVisitor: TAstVisitor;   { not owned - supplied by the caller }
    procedure WalkTypeDecls(AList: TObjectList);
    procedure WalkMethods(AList: TObjectList);
    procedure WalkMethod(AMethod: TMethodDecl);
    procedure WalkStmtList(AList: TObjectList; ADepth: Integer);
    procedure WalkStmt(AStmt: TASTStmt; ADepth: Integer);
  public
    constructor Create(AVisitor: TAstVisitor);
    { Entry point: walk one block's declarations and top-level statements. }
    procedure Walk(ABlock: TBlock);
  end;

implementation

{ ---- TAstVisitor: empty defaults ---- }

procedure TAstVisitor.VisitTypeDecl(ADecl: TTypeDecl);                  begin end;
procedure TAstVisitor.VisitClass(AClass: TClassTypeDef; ADecl: TTypeDecl); begin end;
procedure TAstVisitor.VisitVarDecl(AVar: TVarDecl);                     begin end;
procedure TAstVisitor.VisitConstDecl(AConst: TConstDecl);              begin end;
procedure TAstVisitor.VisitMethodEnter(AMethod: TMethodDecl);          begin end;
procedure TAstVisitor.VisitMethodExit(AMethod: TMethodDecl);           begin end;
procedure TAstVisitor.VisitStmtEnter(AStmt: TASTStmt; ADepth: Integer); begin end;
procedure TAstVisitor.VisitStmtExit(AStmt: TASTStmt; ADepth: Integer);  begin end;

{ ---- TAstWalker ---- }

constructor TAstWalker.Create(AVisitor: TAstVisitor);
begin
  inherited Create();
  FVisitor := AVisitor;
end;

procedure TAstWalker.Walk(ABlock: TBlock);
var
  I: Integer;
begin
  if ABlock = nil then
    Exit;
  WalkTypeDecls(ABlock.TypeDecls);

  if ABlock.ConstDecls <> nil then
    for I := 0 to ABlock.ConstDecls.Count - 1 do
      FVisitor.VisitConstDecl(TConstDecl(ABlock.ConstDecls[I]));

  if ABlock.Decls <> nil then
    for I := 0 to ABlock.Decls.Count - 1 do
      FVisitor.VisitVarDecl(TVarDecl(ABlock.Decls[I]));

  WalkMethods(ABlock.ProcDecls);
  WalkStmtList(ABlock.Stmts, 1);
end;

procedure TAstWalker.WalkTypeDecls(AList: TObjectList);
var
  I:    Integer;
  Decl: TTypeDecl;
begin
  if AList = nil then
    Exit;
  for I := 0 to AList.Count - 1 do
  begin
    Decl := TTypeDecl(AList[I]);
    FVisitor.VisitTypeDecl(Decl);
    if (Decl.Def <> nil) and (Decl.Def is TClassTypeDef) then
      FVisitor.VisitClass(TClassTypeDef(Decl.Def), Decl);
  end;
end;

procedure TAstWalker.WalkMethods(AList: TObjectList);
var
  I: Integer;
begin
  if AList = nil then
    Exit;
  for I := 0 to AList.Count - 1 do
    WalkMethod(TMethodDecl(AList[I]));
end;

procedure TAstWalker.WalkMethod(AMethod: TMethodDecl);
begin
  FVisitor.VisitMethodEnter(AMethod);
  if AMethod.Body <> nil then
  begin
    { A routine body is itself a block: nested types/consts/vars/procs plus
      the statement list.  Recurse so nested procedures are visited too. }
    Walk(AMethod.Body);
  end;
  FVisitor.VisitMethodExit(AMethod);
end;

procedure TAstWalker.WalkStmtList(AList: TObjectList; ADepth: Integer);
var
  I: Integer;
begin
  if AList = nil then
    Exit;
  for I := 0 to AList.Count - 1 do
    WalkStmt(TASTStmt(AList[I]), ADepth);
end;

procedure TAstWalker.WalkStmt(AStmt: TASTStmt; ADepth: Integer);
var
  J: Integer;
begin
  if AStmt = nil then
    Exit;

  FVisitor.VisitStmtEnter(AStmt, ADepth);

  { Descend into nested statements.  Control-flow constructs raise the depth
    for their bodies; a compound (begin/end) is transparent. }
  if AStmt is TCompoundStmt then
    WalkStmtList(TCompoundStmt(AStmt).Stmts, ADepth)

  else if AStmt is TIfStmt then
  begin
    WalkStmt(TIfStmt(AStmt).ThenStmt, ADepth + 1);
    WalkStmt(TIfStmt(AStmt).ElseStmt, ADepth + 1);
  end

  else if AStmt is TWhileStmt then
    WalkStmt(TWhileStmt(AStmt).Body, ADepth + 1)

  else if AStmt is TForStmt then
    WalkStmt(TForStmt(AStmt).Body, ADepth + 1)

  else if AStmt is TForInStmt then
    WalkStmt(TForInStmt(AStmt).Body, ADepth + 1)

  else if AStmt is TRepeatStmt then
    WalkStmtList(TRepeatStmt(AStmt).Body.Stmts, ADepth + 1)

  else if AStmt is TCaseStmt then
  begin
    for J := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      WalkStmt(TCaseBranch(TCaseStmt(AStmt).Branches[J]).Stmt, ADepth + 1);
    WalkStmt(TCaseStmt(AStmt).ElseStmt, ADepth + 1);
  end

  else if AStmt is TTryFinallyStmt then
  begin
    WalkStmtList(TTryFinallyStmt(AStmt).TryBody.Stmts, ADepth + 1);
    WalkStmtList(TTryFinallyStmt(AStmt).FinallyBody.Stmts, ADepth + 1);
  end

  else if AStmt is TTryExceptStmt then
  begin
    WalkStmtList(TTryExceptStmt(AStmt).TryBody.Stmts, ADepth + 1);
    if TTryExceptStmt(AStmt).Handlers <> nil then
      for J := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
        WalkStmtList(
          TExceptHandlerClause(TTryExceptStmt(AStmt).Handlers[J]).Body.Stmts,
          ADepth + 1);
    if TTryExceptStmt(AStmt).ExceptBody <> nil then
      WalkStmtList(TTryExceptStmt(AStmt).ExceptBody.Stmts, ADepth + 1);
    if TTryExceptStmt(AStmt).ElseBody <> nil then
      WalkStmtList(TTryExceptStmt(AStmt).ElseBody.Stmts, ADepth + 1);
  end;
  { Leaf statements (assignment, calls, raise, exit, break, ...) carry only
    expressions, which the statement walk does not descend. }

  FVisitor.VisitStmtExit(AStmt, ADepth);
end;

end.
