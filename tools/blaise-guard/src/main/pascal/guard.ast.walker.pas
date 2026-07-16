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
    { Called (pre-order) for every expression node reachable from a statement,
      including the sub-expressions of calls, operators and subscripts. }
    procedure VisitExpr(AExpr: TASTExpr); virtual;
  end;

  TAstWalker = class
  private
    [Unretained] FVisitor: TAstVisitor;   { not owned - supplied by the caller }
    procedure WalkTypeDecls(AList: TObjectList);
    procedure WalkMethods(AList: TObjectList);
    procedure WalkMethod(AMethod: TMethodDecl);
    procedure WalkStmtList(AList: TObjectList; ADepth: Integer);
    procedure WalkStmt(AStmt: TASTStmt; ADepth: Integer);
    procedure WalkStmtExprs(AStmt: TASTStmt);
    procedure WalkExpr(AExpr: TASTExpr);
    procedure WalkArgs(AList: TObjectList);
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
procedure TAstVisitor.VisitExpr(AExpr: TASTExpr);                       begin end;

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

  { Visit the expressions this statement holds (conditions, RHS, call args). }
  WalkStmtExprs(AStmt);

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
    expressions, which WalkStmtExprs handled above. }

  FVisitor.VisitStmtExit(AStmt, ADepth);
end;

procedure TAstWalker.WalkStmtExprs(AStmt: TASTStmt);
var
  J: Integer;
begin
  if AStmt is TAssignment then
    WalkExpr(TAssignment(AStmt).Expr)

  else if AStmt is TIfStmt then
    WalkExpr(TIfStmt(AStmt).Condition)

  else if AStmt is TWhileStmt then
    WalkExpr(TWhileStmt(AStmt).Condition)

  else if AStmt is TRepeatStmt then
    WalkExpr(TRepeatStmt(AStmt).Condition)

  else if AStmt is TForStmt then
  begin
    WalkExpr(TForStmt(AStmt).StartExpr);
    WalkExpr(TForStmt(AStmt).EndExpr);
  end

  else if AStmt is TForInStmt then
    WalkExpr(TForInStmt(AStmt).CollExpr)

  else if AStmt is TCaseStmt then
  begin
    WalkExpr(TCaseStmt(AStmt).Selector);
    for J := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      WalkArgs(TCaseBranch(TCaseStmt(AStmt).Branches[J]).Values);
  end

  else if AStmt is TRaiseStmt then
    WalkExpr(TRaiseStmt(AStmt).Expr)

  else if AStmt is TExitStmt then
    WalkExpr(TExitStmt(AStmt).Value)

  else if AStmt is TProcCall then
    WalkArgs(TProcCall(AStmt).Args)

  else if AStmt is TMethodCallStmt then
  begin
    WalkExpr(TMethodCallStmt(AStmt).ObjExpr);
    WalkArgs(TMethodCallStmt(AStmt).Args);
  end

  else if AStmt is TInheritedCallStmt then
    WalkArgs(TInheritedCallStmt(AStmt).Args)

  else if AStmt is TFieldAssignment then
  begin
    WalkExpr(TFieldAssignment(AStmt).Expr);
    WalkExpr(TFieldAssignment(AStmt).ObjExpr);
    WalkExpr(TFieldAssignment(AStmt).PropIndexExpr);
  end

  else if AStmt is TStaticSubscriptAssign then
  begin
    WalkExpr(TStaticSubscriptAssign(AStmt).IndexExpr);
    WalkExpr(TStaticSubscriptAssign(AStmt).ValueExpr);
    WalkExpr(TStaticSubscriptAssign(AStmt).BaseExpr);
  end

  else if AStmt is TVarDeclStmt then
    WalkExpr(TVarDeclStmt(AStmt).InitExpr)

  else if AStmt is TPointerWriteStmt then
  begin
    WalkExpr(TPointerWriteStmt(AStmt).PtrExpr);
    WalkExpr(TPointerWriteStmt(AStmt).ValExpr);
  end;
end;

procedure TAstWalker.WalkArgs(AList: TObjectList);
var
  I: Integer;
begin
  if AList = nil then
    Exit;
  for I := 0 to AList.Count - 1 do
    WalkExpr(TASTExpr(AList[I]));
end;

procedure TAstWalker.WalkExpr(AExpr: TASTExpr);
var
  AM: TAnonMethodExpr;
begin
  if AExpr = nil then
    Exit;

  FVisitor.VisitExpr(AExpr);

  if AExpr is TBinaryExpr then
  begin
    WalkExpr(TBinaryExpr(AExpr).Left);
    WalkExpr(TBinaryExpr(AExpr).Right);
  end

  else if AExpr is TNotExpr then
    WalkExpr(TNotExpr(AExpr).Expr)

  else if AExpr is TFieldAccessExpr then
    WalkExpr(TFieldAccessExpr(AExpr).Base)

  else if AExpr is TStringSubscriptExpr then
  begin
    WalkExpr(TStringSubscriptExpr(AExpr).StrExpr);
    WalkExpr(TStringSubscriptExpr(AExpr).IndexExpr);
  end

  else if AExpr is TArrayLiteralExpr then
    WalkArgs(TArrayLiteralExpr(AExpr).Elements)

  else if AExpr is TSetRangeExpr then
  begin
    WalkExpr(TSetRangeExpr(AExpr).LowExpr);
    WalkExpr(TSetRangeExpr(AExpr).HighExpr);
  end

  else if AExpr is TIsExpr then
    WalkExpr(TIsExpr(AExpr).Obj)

  else if AExpr is TAsExpr then
    WalkExpr(TAsExpr(AExpr).Obj)

  else if AExpr is TSupportsExpr then
    WalkExpr(TSupportsExpr(AExpr).Obj)

  else if AExpr is TInheritedCallExpr then
    WalkArgs(TInheritedCallExpr(AExpr).Args)

  else if AExpr is TFuncCallExpr then
    WalkArgs(TFuncCallExpr(AExpr).Args)

  else if AExpr is TIndirectFuncCallExpr then
  begin
    WalkExpr(TIndirectFuncCallExpr(AExpr).CalleeExpr);
    WalkArgs(TIndirectFuncCallExpr(AExpr).Args);
  end

  else if AExpr is TDerefExpr then
    WalkExpr(TDerefExpr(AExpr).Expr)

  else if AExpr is TAddrOfExpr then
    WalkExpr(TAddrOfExpr(AExpr).Expr)

  else if AExpr is TMethodCallExpr then
  begin
    WalkExpr(TMethodCallExpr(AExpr).ObjExpr);
    WalkArgs(TMethodCallExpr(AExpr).Args);
  end

  else if AExpr is TAnonMethodExpr then
  begin
    { An anonymous method is its own scope: walk it as a nested routine so a
      rule sees its params/locals and, crucially, its captured uses of the
      enclosing scope's variables. }
    AM := TAnonMethodExpr(AExpr);
    if AM.Decl <> nil then
    begin
      FVisitor.VisitMethodEnter(AM.Decl);
      if AM.Decl.Body <> nil then
        Walk(AM.Decl.Body);
      if AM.ArrowExpr <> nil then
        WalkExpr(AM.ArrowExpr);
      FVisitor.VisitMethodExit(AM.Decl);
    end;
  end;
  { Leaf expressions (TIdentExpr, literals, TNilLiteral) have no children. }
end;

end.
