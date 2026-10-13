{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.arcshapes;

{ Backend-independent ARC shape analysis shared by the QBE and native code
  generators.

  TConstArgMode classifies how a caller must protect a const-string argument
  for the duration of a call once the callee no longer retains const params:

    camBorrowed — the argument's buffer is guaranteed to outlive the call
                  without help (string literals, named consts, plain
                  non-aliased local variables): emit no ARC ops at all.
    camConsume  — the argument is a +1 owned temporary (function/method/
                  getter return): emit no AddRef, ONE release after the
                  call consumes the temp.
    camPin      — anything aliasable or unowned (globals, fields, concat
                  transients, address-taken or captured locals): AddRef
                  before the call, release after.

  CollectAddressTaken walks a function body and returns every local whose
  address escapes — via explicit @, or by being passed to a var/out param.
  Both backends use it: the QBE backend for mem2reg promotion and the
  borrowed-argument blocklist, the native backend for the borrowed-argument
  blocklist. }

interface

uses
  Classes, SysUtils, uAST, uSymbolTable;

type
  TConstArgMode = (camPin, camBorrowed, camConsume);

procedure CollectAddressTakenExpr(AExpr: TASTExpr; ASet: TStringList);
procedure CollectAddressTakenStmt(AStmt: TASTStmt; ASet: TStringList);
{ Returns a new sorted, case-sensitive, dup-ignoring list; caller frees. }
function CollectAddressTaken(ABlock: TBlock): TStringList;

implementation

{ Mark AArg when it is a plain local ident passed by reference. }
procedure MarkVarArg(AArg: TASTExpr; ASet: TStringList);
begin
  if (AArg is TIdentExpr) and not TIdentExpr(AArg).IsGlobal then
    ASet.Add(TIdentExpr(AArg).Name);
end;

{ Interface (itab) dispatch has no ResolvedMethod: recover the var/out
  param flags from the interface type's method table (parent chain
  included) and mark local args passed by reference. }
procedure MarkIntfVarArgs(AIntf: TTypeDesc; const AMethName: string;
  AArgs: TObjectList; ASet: TStringList);
var
  It: TInterfaceTypeDesc;
  MI, I: Integer;
begin
  if (AIntf = nil) or (AIntf.Kind <> tyInterface) or (AArgs = nil) then Exit;
  It := TInterfaceTypeDesc(AIntf);
  MI := -1;
  while It <> nil do
  begin
    MI := It.MethodIndex(AMethName);
    if MI >= 0 then Break;
    It := It.Parent;
  end;
  if MI < 0 then Exit;
  for I := 0 to AArgs.Count - 1 do
    if It.MethodParamIsVar(MI, I) then
      MarkVarArg(TASTExpr(AArgs.Items[I]), ASet);
end;

{ Indirect / proc-field calls: recover var-param modes from the
  procedural type's signature. }
procedure MarkProcTypeVarArgs(AProcType: TObject; AArgs: TObjectList;
  ASet: TStringList);
var
  PT: TProceduralTypeDesc;
  I: Integer;
begin
  if (AProcType = nil) or (AArgs = nil) then Exit;
  PT := TProceduralTypeDesc(AProcType);
  if PT.Params = nil then Exit;
  for I := 0 to AArgs.Count - 1 do
    if (I < PT.Params.Count) and
       TProcParamInfo(PT.Params.Items[I]).IsVarParam then
      MarkVarArg(TASTExpr(AArgs.Items[I]), ASet);
end;

procedure CollectAddressTakenExpr(AExpr: TASTExpr; ASet: TStringList);
var
  I: Integer;
  FC: TFuncCallExpr;
  MC: TMethodCallExpr;
  FA: TFieldAccessExpr;
  Param: TMethodParam;
  Arg: TASTExpr;
begin
  if AExpr = nil then Exit;

  { @X — explicit address-of }
  if AExpr is TAddrOfExpr then
  begin
    if TAddrOfExpr(AExpr).Expr is TIdentExpr then
      ASet.Add(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
    CollectAddressTakenExpr(TAddrOfExpr(AExpr).Expr, ASet);
    Exit;
  end;

  { Function call: var params take the address of their actual argument }
  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    if FC.ResolvedDecl <> nil then
    begin
      for I := 0 to FC.Args.Count - 1 do
      begin
        Arg := TASTExpr(FC.Args.Items[I]);
        if I < TMethodDecl(FC.ResolvedDecl).Params.Count then
        begin
          Param := TMethodParam(TMethodDecl(FC.ResolvedDecl).Params.Items[I]);
          if Param.IsVarParam and (Arg is TIdentExpr) and not TIdentExpr(Arg).IsGlobal then
            ASet.Add(TIdentExpr(Arg).Name);
        end;
        CollectAddressTakenExpr(Arg, ASet);
      end;
    end
    else
    begin
      { Indirect call through a procedural variable/field: the signature
        lives on the procedural type, not a decl. }
      if (FC.IsIndirectCall or FC.IsProcFieldCall) and
         (FC.ResolvedProcType <> nil) then
        MarkProcTypeVarArgs(FC.ResolvedProcType, FC.Args, ASet);
      for I := 0 to FC.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(FC.Args.Items[I]), ASet);
    end;
    Exit;
  end;

  { Method call: same var-param check }
  if AExpr is TMethodCallExpr then
  begin
    MC := TMethodCallExpr(AExpr);
    CollectAddressTakenExpr(MC.ObjExpr, ASet);
    if MC.ResolvedMethod <> nil then
    begin
      for I := 0 to MC.Args.Count - 1 do
      begin
        Arg := TASTExpr(MC.Args.Items[I]);
        if I < TMethodDecl(MC.ResolvedMethod).Params.Count then
        begin
          Param := TMethodParam(TMethodDecl(MC.ResolvedMethod).Params.Items[I]);
          if Param.IsVarParam and (Arg is TIdentExpr) and not TIdentExpr(Arg).IsGlobal then
            ASet.Add(TIdentExpr(Arg).Name);
        end;
        CollectAddressTakenExpr(Arg, ASet);
      end;
    end
    else
    begin
      { Interface (itab) dispatch and proc-field calls carry no
        ResolvedMethod — recover param modes from the type. }
      MarkIntfVarArgs(MC.ResolvedClassType, MC.Name, MC.Args, ASet);
      if MC.IsProcFieldCall and (MC.ResolvedProcType <> nil) then
        MarkProcTypeVarArgs(MC.ResolvedProcType, MC.Args, ASet);
      for I := 0 to MC.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(MC.Args.Items[I]), ASet);
    end;
    Exit;
  end;

  { Recurse into common composite expressions }
  if AExpr is TBinaryExpr then
  begin
    CollectAddressTakenExpr(TBinaryExpr(AExpr).Left, ASet);
    CollectAddressTakenExpr(TBinaryExpr(AExpr).Right, ASet);
  end
  else if AExpr is TNotExpr then
    CollectAddressTakenExpr(TNotExpr(AExpr).Expr, ASet)
  else if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    CollectAddressTakenExpr(FA.Base, ASet);
    if FA.PropIndexExpr <> nil then
      CollectAddressTakenExpr(FA.PropIndexExpr, ASet);
  end
  else if AExpr is TDerefExpr then
    CollectAddressTakenExpr(TDerefExpr(AExpr).Expr, ASet)
  else if AExpr is TStringSubscriptExpr then
  begin
    CollectAddressTakenExpr(TStringSubscriptExpr(AExpr).StrExpr, ASet);
    CollectAddressTakenExpr(TStringSubscriptExpr(AExpr).IndexExpr, ASet);
  end
  else if AExpr is TIsExpr then
    CollectAddressTakenExpr(TIsExpr(AExpr).Obj, ASet)
  else if AExpr is TAsExpr then
    CollectAddressTakenExpr(TAsExpr(AExpr).Obj, ASet)
  else if AExpr is TSupportsExpr then
    CollectAddressTakenExpr(TSupportsExpr(AExpr).Obj, ASet)
  else if AExpr is TArrayLiteralExpr then
    for I := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      CollectAddressTakenExpr(TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[I]), ASet);
end;

procedure CollectAddressTakenStmt(AStmt: TASTStmt; ASet: TStringList);
var
  I:      Integer;
  TryE:   TTryExceptStmt;
  TryF:   TTryFinallyStmt;
  RaiseS: TRaiseStmt;
  CaseS:  TCaseStmt;
  PWrite: TPointerWriteStmt;
  SSubA:  TStaticSubscriptAssign;
  PCall:  TProcCall;
  MCall:  TMethodCallStmt;
  ICall:  TInheritedCallStmt;
  ForS:   TForStmt;
begin
  if AStmt = nil then Exit;

  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      CollectAddressTakenStmt(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]), ASet);
  end
  else if AStmt is TIfStmt then
  begin
    CollectAddressTakenExpr(TIfStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TIfStmt(AStmt).ThenStmt, ASet);
    CollectAddressTakenStmt(TIfStmt(AStmt).ElseStmt, ASet);
  end
  else if AStmt is TWhileStmt then
  begin
    CollectAddressTakenExpr(TWhileStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TWhileStmt(AStmt).Body, ASet);
  end
  else if AStmt is TRepeatStmt then
  begin
    CollectAddressTakenExpr(TRepeatStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TRepeatStmt(AStmt).Body, ASet);
  end
  else if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    CollectAddressTakenExpr(ForS.StartExpr, ASet);
    CollectAddressTakenExpr(ForS.EndExpr, ASet);
    CollectAddressTakenStmt(ForS.Body, ASet);
  end
  else if AStmt is TForInStmt then
  begin
    { The loop variable is written through its slot address by the
      for-in lowering (storew/storel into %_var_<name>) — it must stay
      a stack slot, never a promoted SSA temp. }
    if ASet.IndexOf(TForInStmt(AStmt).VarName) < 0 then
      ASet.Add(TForInStmt(AStmt).VarName);
    CollectAddressTakenExpr(TForInStmt(AStmt).CollExpr, ASet);
    CollectAddressTakenStmt(TForInStmt(AStmt).Body, ASet);
  end
  else if AStmt is TAssignment then
    CollectAddressTakenExpr(TAssignment(AStmt).Expr, ASet)
  else if AStmt is TFieldAssignment then
    CollectAddressTakenExpr(TFieldAssignment(AStmt).Expr, ASet)
  else if AStmt is TMethodCallStmt then
  begin
    MCall := TMethodCallStmt(AStmt);
    CollectAddressTakenExpr(MCall.ObjExpr, ASet);
    if MCall.ResolvedMethod <> nil then
      for I := 0 to MCall.Args.Count - 1 do
      begin
        if I < TMethodDecl(MCall.ResolvedMethod).Params.Count then
          if TMethodParam(TMethodDecl(MCall.ResolvedMethod).Params.Items[I]).IsVarParam and
             (TASTExpr(MCall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(MCall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(MCall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(MCall.Args.Items[I]), ASet);
      end
    else
    begin
      MarkIntfVarArgs(MCall.ResolvedClassType, MCall.Name, MCall.Args, ASet);
      if MCall.IsProcFieldCall and (MCall.ResolvedProcType <> nil) then
        MarkProcTypeVarArgs(MCall.ResolvedProcType, MCall.Args, ASet);
      for I := 0 to MCall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(MCall.Args.Items[I]), ASet);
    end;
  end
  else if AStmt is TProcCall then
  begin
    PCall := TProcCall(AStmt);
    if PCall.ResolvedDecl <> nil then
      for I := 0 to PCall.Args.Count - 1 do
      begin
        if I < TMethodDecl(PCall.ResolvedDecl).Params.Count then
          if TMethodParam(TMethodDecl(PCall.ResolvedDecl).Params.Items[I]).IsVarParam and
             (TASTExpr(PCall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(PCall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(PCall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(PCall.Args.Items[I]), ASet);
      end
    else
    begin
      if (PCall.IsIndirectCall or PCall.IsProcFieldCall) and
         (PCall.ResolvedProcType <> nil) then
        MarkProcTypeVarArgs(PCall.ResolvedProcType, PCall.Args, ASet);
      for I := 0 to PCall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(PCall.Args.Items[I]), ASet);
    end;
  end
  else if AStmt is TInheritedCallStmt then
  begin
    ICall := TInheritedCallStmt(AStmt);
    if ICall.ResolvedMethod <> nil then
      for I := 0 to ICall.Args.Count - 1 do
      begin
        if I < TMethodDecl(ICall.ResolvedMethod).Params.Count then
          if TMethodParam(TMethodDecl(ICall.ResolvedMethod).Params.Items[I]).IsVarParam and
             (TASTExpr(ICall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(ICall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(ICall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(ICall.Args.Items[I]), ASet);
      end
    else
      for I := 0 to ICall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(ICall.Args.Items[I]), ASet);
  end
  else if AStmt is TTryFinallyStmt then
  begin
    TryF := TTryFinallyStmt(AStmt);
    CollectAddressTakenStmt(TryF.TryBody, ASet);
    CollectAddressTakenStmt(TryF.FinallyBody, ASet);
  end
  else if AStmt is TTryExceptStmt then
  begin
    TryE := TTryExceptStmt(AStmt);
    CollectAddressTakenStmt(TryE.TryBody, ASet);
    for I := 0 to TryE.Handlers.Count - 1 do
      CollectAddressTakenStmt(TExceptHandlerClause(TryE.Handlers.Items[I]).Body, ASet);
    CollectAddressTakenStmt(TryE.ElseBody, ASet);
    CollectAddressTakenStmt(TryE.ExceptBody, ASet);
  end
  else if AStmt is TRaiseStmt then
  begin
    RaiseS := TRaiseStmt(AStmt);
    CollectAddressTakenExpr(RaiseS.Expr, ASet);
  end
  else if AStmt is TCaseStmt then
  begin
    CaseS := TCaseStmt(AStmt);
    CollectAddressTakenExpr(CaseS.Selector, ASet);
    for I := 0 to CaseS.Branches.Count - 1 do
      CollectAddressTakenStmt(TCaseBranch(CaseS.Branches.Items[I]).Stmt, ASet);
    CollectAddressTakenStmt(CaseS.ElseStmt, ASet);
  end
  else if AStmt is TExprCallStmt then
    CollectAddressTakenExpr(TExprCallStmt(AStmt).Call, ASet)
  else if AStmt is TPointerWriteStmt then
  begin
    PWrite := TPointerWriteStmt(AStmt);
    CollectAddressTakenExpr(PWrite.PtrExpr, ASet);
    CollectAddressTakenExpr(PWrite.ValExpr, ASet);
  end
  else if AStmt is TStaticSubscriptAssign then
  begin
    SSubA := TStaticSubscriptAssign(AStmt);
    CollectAddressTakenExpr(SSubA.IndexExpr, ASet);
    CollectAddressTakenExpr(SSubA.ValueExpr, ASet);
  end
  else if (AStmt is TExitStmt) and (TExitStmt(AStmt).ResultAssign <> nil) then
    { Exit(X) carries a synthesised 'Result := X' — walk it. }
    CollectAddressTakenStmt(TExitStmt(AStmt).ResultAssign, ASet);
  { TBreakStmt, TContinueStmt, bare TExitStmt — no expressions to walk }
end;

function CollectAddressTaken(ABlock: TBlock): TStringList;
var
  I: Integer;
begin
  Result := TStringList.Create();
  Result.CaseSensitive := True;
  Result.Duplicates := dupIgnore;
  Result.Sorted := True;
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Stmts.Count - 1 do
    CollectAddressTakenStmt(TASTStmt(ABlock.Stmts.Items[I]), Result);
end;

end.
