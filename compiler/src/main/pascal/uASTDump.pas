{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uASTDump;

interface

uses
  uAST, uSymbolTable;

procedure DumpProgram(AProg: TProgram);
procedure DumpUnit(AUnit: TUnit);

implementation

uses
  Classes, SysUtils, contnrs;

var
  IndentLevel: Integer;

procedure Indent;
var
  I: Integer;
begin
  for I := 1 to IndentLevel do
    Write('  ');
end;

procedure Line(const S: string);
begin
  Indent();
  WriteLn(S);
end;

function TypeStr(T: TTypeDesc): string;
begin
  if T = nil then
    Exit('<nil>');
  Result := T.Name;
  case T.Kind of
    tyInteger:    Result := Result + ':Integer';
    tyInt64:      Result := Result + ':Int64';
    tyUInt32:     Result := Result + ':UInt32';
    tyUInt64:     Result := Result + ':UInt64';
    tySmallInt:   Result := Result + ':SmallInt';
    tyInt8:       Result := Result + ':Int8';
    tyWord:       Result := Result + ':Word';
    tyByte:       Result := Result + ':Byte';
    tyBoolean:    Result := Result + ':Boolean';
    tyDouble:     Result := Result + ':Double';
    tyString:     Result := Result + ':String';
    tyPointer:    Result := Result + ':Pointer';
    tyNil:        Result := Result + ':nil';
    tyVoid:       Result := Result + ':void';
    tyClass:      Result := Result + ':class';
    tyRecord:     Result := Result + ':record';
    tyInterface:  Result := Result + ':interface';
    tyDynArray:   Result := Result + ':dynarray';
    tyStaticArray: Result := Result + ':array';
    tyOpenArray:  Result := Result + ':openarray';
    tyProcedural: Result := Result + ':procedural';
    tyPChar:      Result := Result + ':PChar';
    tyEnum:       Result := Result + ':enum';
    tySet:        Result := Result + ':set';
  else
    Result := Result + ':?';
  end;
  if T.RawSize() > 0 then
    Result := Result + '(' + IntToStr(T.RawSize()) + 'B)';
end;

function FieldStr(F: TFieldInfo): string;
begin
  if F = nil then
    Exit('<nil>');
  Result := F.Name + '@' + IntToStr(F.Offset);
  if F.TypeDesc <> nil then
    Result := Result + ':' + TypeStr(F.TypeDesc);
end;

procedure DumpExpr(AExpr: TASTExpr); forward;
procedure DumpStmt(AStmt: TASTStmt); forward;
procedure DumpBlock(ABlock: TBlock); forward;

procedure DumpFlags(AExpr: TASTExpr);
var
  Flags: string;
begin
  Flags := '';
  if AExpr.ResolvedType <> nil then
    Flags := Flags + ' type=' + TypeStr(AExpr.ResolvedType);
  if Flags <> '' then
    Write(Flags);
end;

procedure DumpExpr(AExpr: TASTExpr);
var
  I: Integer;
  Flags: string;
begin
  if AExpr = nil then
  begin
    Line('<nil-expr>');
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    Line('IntLiteral(' + IntToStr(TIntLiteral(AExpr).Value) + ')');
    Exit;
  end;

  if AExpr is TFloatLiteral then
  begin
    Line('FloatLiteral(' + TFloatLiteral(AExpr).Value + ')');
    Exit;
  end;

  if AExpr is TStringLiteral then
  begin
    Line('StringLiteral("' + TStringLiteral(AExpr).Value + '")');
    Exit;
  end;

  if AExpr is TNilLiteral then
  begin
    Line('NilLiteral');
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    Flags := '';
    if TIdentExpr(AExpr).IsImplicitSelf then
    begin
      Flags := Flags + ' ImplicitSelf';
      if TIdentExpr(AExpr).ImplicitFieldInfo <> nil then
        Flags := Flags + '(' + FieldStr(TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo)) + ')';
    end;
    if TIdentExpr(AExpr).IsImplicitSelfMethod then
      Flags := Flags + ' ImplicitSelfMethod';
    if TIdentExpr(AExpr).ParamMode <> pmNone then
      Flags := Flags + ' VarParam';
    if TIdentExpr(AExpr).IsGlobal then
      Flags := Flags + ' Global';
    if TIdentExpr(AExpr).IsConstant then
      Flags := Flags + ' Const';
    Indent();
    Write('Ident(' + TIdentExpr(AExpr).Name + ')');
    DumpFlags(AExpr);
    Write(Flags);
    WriteLn();
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Flags := '';
    if TFieldAccessExpr(AExpr).IsImplicitSelf then
    begin
      Flags := Flags + ' ImplicitSelf';
      if TFieldAccessExpr(AExpr).ImplicitBaseInfo <> nil then
        Flags := Flags + '(base=' + FieldStr(TFieldAccessExpr(AExpr).ImplicitBaseInfo) + ')';
    end;
    if TFieldAccessExpr(AExpr).IsClassAccess then
      Flags := Flags + ' ClassAccess';
    if TFieldAccessExpr(AExpr).IsVarParam then
      Flags := Flags + ' VarParam';
    if TFieldAccessExpr(AExpr).IsMethodCall then
      Flags := Flags + ' MethodCall';
    if TFieldAccessExpr(AExpr).IsConstructorCall then
      Flags := Flags + ' CtorCall';
    if TFieldAccessExpr(AExpr).IsArrayAccess then
      Flags := Flags + ' ArrayAccess';
    if TFieldAccessExpr(AExpr).FieldInfo <> nil then
      Flags := Flags + ' field=' + FieldStr(TFieldAccessExpr(AExpr).FieldInfo);
    Indent();
    Write('FieldAccess(');
    if TFieldAccessExpr(AExpr).RecordName <> '' then
      Write(TFieldAccessExpr(AExpr).RecordName + '.');
    Write(TFieldAccessExpr(AExpr).FieldName + ')');
    DumpFlags(AExpr);
    Write(Flags);
    WriteLn();
    if TFieldAccessExpr(AExpr).Base <> nil then
    begin
      Inc(IndentLevel);
      Line('Base:');
      Inc(IndentLevel);
      DumpExpr(TFieldAccessExpr(AExpr).Base);
      Dec(IndentLevel);
      Dec(IndentLevel);
    end;
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    Indent();
    Write('BinaryExpr(' + BinaryOpName(TBinaryExpr(AExpr).Op) + ')');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TBinaryExpr(AExpr).Left);
    DumpExpr(TBinaryExpr(AExpr).Right);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TNotExpr then
  begin
    Indent();
    Write('Not');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TNotExpr(AExpr).Expr);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TStringSubscriptExpr then
  begin
    Indent();
    Write('Subscript');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TStringSubscriptExpr(AExpr).StrExpr);
    DumpExpr(TStringSubscriptExpr(AExpr).IndexExpr);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TArrayLiteralExpr then
  begin
    Indent();
    Write('ArrayLiteral');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    for I := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      DumpExpr(TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TMethodCallExpr then
  begin
    Flags := '';
    if TMethodCallExpr(AExpr).IsConstructorCall then
      Flags := Flags + ' Ctor';
    if TMethodCallExpr(AExpr).IsGlobal then
      Flags := Flags + ' Global';
    if TMethodCallExpr(AExpr).IsVarParam then
      Flags := Flags + ' VarParam';
    if TMethodCallExpr(AExpr).ResolvedClassType <> nil then
      Flags := Flags + ' class=' + TypeStr(TMethodCallExpr(AExpr).ResolvedClassType);
    Indent();
    Write('MethodCallExpr(');
    if TMethodCallExpr(AExpr).ObjectName <> '' then
      Write(TMethodCallExpr(AExpr).ObjectName + '.');
    Write(TMethodCallExpr(AExpr).Name + ')');
    DumpFlags(AExpr);
    Write(Flags);
    WriteLn();
    Inc(IndentLevel);
    if TMethodCallExpr(AExpr).ObjExpr <> nil then
    begin
      Line('Receiver:');
      Inc(IndentLevel);
      DumpExpr(TMethodCallExpr(AExpr).ObjExpr);
      Dec(IndentLevel);
    end;
    for I := 0 to TMethodCallExpr(AExpr).Args.Count - 1 do
      DumpExpr(TASTExpr(TMethodCallExpr(AExpr).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    Indent();
    Write('FuncCall(' + TFuncCallExpr(AExpr).Name + ')');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
      DumpExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TDerefExpr then
  begin
    Indent();
    Write('Deref');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TDerefExpr(AExpr).Expr);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TAddrOfExpr then
  begin
    Indent();
    Write('AddrOf');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TAddrOfExpr(AExpr).Expr);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TIsExpr then
  begin
    Indent();
    Write('Is(' + TIsExpr(AExpr).TypeName + ')');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TIsExpr(AExpr).Obj);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TAsExpr then
  begin
    Indent();
    Write('As(' + TAsExpr(AExpr).TypeName + ')');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TAsExpr(AExpr).Obj);
    Dec(IndentLevel);
    Exit;
  end;

  if AExpr is TIndirectFuncCallExpr then
  begin
    Indent();
    Write('IndirectCall');
    DumpFlags(AExpr);
    WriteLn();
    Inc(IndentLevel);
    DumpExpr(TIndirectFuncCallExpr(AExpr).CalleeExpr);
    for I := 0 to TIndirectFuncCallExpr(AExpr).Args.Count - 1 do
      DumpExpr(TASTExpr(TIndirectFuncCallExpr(AExpr).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  Indent();
  Write(AExpr.ClassName);
  DumpFlags(AExpr);
  WriteLn();
end;

procedure DumpStmt(AStmt: TASTStmt);
var
  I: Integer;
  Flags: string;
begin
  if AStmt = nil then
  begin
    Line('<nil-stmt>');
    Exit;
  end;

  if AStmt is TCompoundStmt then
  begin
    Line('Begin');
    Inc(IndentLevel);
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      DumpStmt(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]));
    Dec(IndentLevel);
    Line('End');
    Exit;
  end;

  if AStmt is TAssignment then
  begin
    Flags := '';
    if TAssignment(AStmt).ImplicitSelfField <> nil then
      Flags := Flags + ' ImplicitSelfField(' + FieldStr(TFieldInfo(TAssignment(AStmt).ImplicitSelfField)) + ')';
    if TAssignment(AStmt).IsVarParam then
      Flags := Flags + ' VarParam';
    if TAssignment(AStmt).IsGlobal then
      Flags := Flags + ' Global';
    if TAssignment(AStmt).ResolvedLhsType <> nil then
      Flags := Flags + ' lhs=' + TypeStr(TAssignment(AStmt).ResolvedLhsType);
    Line('Assign(' + TAssignment(AStmt).Name + ')' + Flags);
    Inc(IndentLevel);
    DumpExpr(TAssignment(AStmt).Expr);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TFieldAssignment then
  begin
    Flags := '';
    if TFieldAssignment(AStmt).IsImplicitSelf then
    begin
      Flags := Flags + ' ImplicitSelf';
      if TFieldAssignment(AStmt).ImplicitBaseInfo <> nil then
        Flags := Flags + '(base=' + FieldStr(TFieldAssignment(AStmt).ImplicitBaseInfo) + ')';
    end;
    if TFieldAssignment(AStmt).IsClassAccess then
      Flags := Flags + ' ClassAccess';
    if TFieldAssignment(AStmt).FieldInfo <> nil then
      Flags := Flags + ' field=' + FieldStr(TFieldAssignment(AStmt).FieldInfo);
    Line('FieldAssign(' + TFieldAssignment(AStmt).RecordName + '.' + TFieldAssignment(AStmt).FieldName + ')' + Flags);
    Inc(IndentLevel);
    DumpExpr(TFieldAssignment(AStmt).Expr);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TIfStmt then
  begin
    Line('If');
    Inc(IndentLevel);
    Line('Cond:');
    Inc(IndentLevel);
    DumpExpr(TIfStmt(AStmt).Condition);
    Dec(IndentLevel);
    Line('Then:');
    Inc(IndentLevel);
    DumpStmt(TIfStmt(AStmt).ThenStmt);
    Dec(IndentLevel);
    if TIfStmt(AStmt).ElseStmt <> nil then
    begin
      Line('Else:');
      Inc(IndentLevel);
      DumpStmt(TIfStmt(AStmt).ElseStmt);
      Dec(IndentLevel);
    end;
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TWhileStmt then
  begin
    Line('While');
    Inc(IndentLevel);
    DumpExpr(TWhileStmt(AStmt).Condition);
    DumpStmt(TWhileStmt(AStmt).Body);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TRepeatStmt then
  begin
    Line('Repeat');
    Inc(IndentLevel);
    for I := 0 to TRepeatStmt(AStmt).Body.Stmts.Count - 1 do
      DumpStmt(TASTStmt(TRepeatStmt(AStmt).Body.Stmts.Items[I]));
    Line('Until:');
    DumpExpr(TRepeatStmt(AStmt).Condition);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TForStmt then
  begin
    Flags := '';
    if TForStmt(AStmt).IsDownTo then
      Flags := ' DownTo';
    Line('For(' + TForStmt(AStmt).VarName + ')' + Flags);
    Inc(IndentLevel);
    Line('From:');
    Inc(IndentLevel);
    DumpExpr(TForStmt(AStmt).StartExpr);
    Dec(IndentLevel);
    Line('To:');
    Inc(IndentLevel);
    DumpExpr(TForStmt(AStmt).EndExpr);
    Dec(IndentLevel);
    DumpStmt(TForStmt(AStmt).Body);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TForInStmt then
  begin
    Line('ForIn(' + TForInStmt(AStmt).VarName + ')');
    Inc(IndentLevel);
    Line('Collection:');
    Inc(IndentLevel);
    DumpExpr(TForInStmt(AStmt).CollExpr);
    Dec(IndentLevel);
    if TForInStmt(AStmt).Lowered <> nil then
      Line('Lowered:');
    DumpStmt(TForInStmt(AStmt).WalkBody());
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TProcCall then
  begin
    Flags := '';
    if TProcCall(AStmt).IsImplicitSelfMethod then
      Flags := Flags + ' ImplicitSelfMethod';
    if TProcCall(AStmt).IsIndirectCall then
      Flags := Flags + ' IndirectCall';
    Line('ProcCall(' + TProcCall(AStmt).Name + ')' + Flags);
    Inc(IndentLevel);
    for I := 0 to TProcCall(AStmt).Args.Count - 1 do
      DumpExpr(TASTExpr(TProcCall(AStmt).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TExprCallStmt then
  begin
    Line('ExprCallStmt');
    Inc(IndentLevel);
    DumpExpr(TExprCallStmt(AStmt).Call);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TMethodCallStmt then
  begin
    Flags := '';
    if TMethodCallStmt(AStmt).IsImplicitSelf then
    begin
      Flags := Flags + ' ImplicitSelf';
      if TMethodCallStmt(AStmt).ImplicitBaseInfo <> nil then
        Flags := Flags + '(base=' + FieldStr(TMethodCallStmt(AStmt).ImplicitBaseInfo) + ')';
    end;
    if TMethodCallStmt(AStmt).IsGlobal then
      Flags := Flags + ' Global';
    if TMethodCallStmt(AStmt).IsVarParam then
      Flags := Flags + ' VarParam';
    if TMethodCallStmt(AStmt).IsProcFieldCall then
      Flags := Flags + ' ProcFieldCall';
    if TMethodCallStmt(AStmt).ResolvedClassType <> nil then
      Flags := Flags + ' class=' + TypeStr(TMethodCallStmt(AStmt).ResolvedClassType);
    if TMethodCallStmt(AStmt).ResolvedMethod <> nil then
      Flags := Flags + ' method=' + TMethodDecl(TMethodCallStmt(AStmt).ResolvedMethod).Name;
    Line('MethodCallStmt(');
    Inc(IndentLevel);
    Indent();
    if TMethodCallStmt(AStmt).ObjectName <> '' then
      Write(TMethodCallStmt(AStmt).ObjectName + '.');
    Write(TMethodCallStmt(AStmt).Name + ')');
    Write(Flags);
    WriteLn();
    for I := 0 to TMethodCallStmt(AStmt).Args.Count - 1 do
      DumpExpr(TASTExpr(TMethodCallStmt(AStmt).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TInheritedCallStmt then
  begin
    Line('InheritedCall(' + TInheritedCallStmt(AStmt).Name + ')');
    Inc(IndentLevel);
    for I := 0 to TInheritedCallStmt(AStmt).Args.Count - 1 do
      DumpExpr(TASTExpr(TInheritedCallStmt(AStmt).Args.Items[I]));
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TExitStmt then
  begin
    if TExitStmt(AStmt).Value <> nil then
    begin
      Line('Exit');
      Inc(IndentLevel);
      DumpExpr(TExitStmt(AStmt).Value);
      Dec(IndentLevel);
    end
    else
      Line('Exit');
    Exit;
  end;

  if AStmt is TBreakStmt then
  begin
    Line('Break');
    Exit;
  end;

  if AStmt is TContinueStmt then
  begin
    Line('Continue');
    Exit;
  end;

  if AStmt is TRaiseStmt then
  begin
    Line('Raise');
    if TRaiseStmt(AStmt).Expr <> nil then
    begin
      Inc(IndentLevel);
      DumpExpr(TRaiseStmt(AStmt).Expr);
      Dec(IndentLevel);
    end;
    Exit;
  end;

  if AStmt is TTryFinallyStmt then
  begin
    Line('TryFinally');
    Inc(IndentLevel);
    Line('Try:');
    Inc(IndentLevel);
    DumpStmt(TTryFinallyStmt(AStmt).TryBody);
    Dec(IndentLevel);
    Line('Finally:');
    Inc(IndentLevel);
    DumpStmt(TTryFinallyStmt(AStmt).FinallyBody);
    Dec(IndentLevel);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TTryExceptStmt then
  begin
    Line('TryExcept');
    Inc(IndentLevel);
    Line('Try:');
    Inc(IndentLevel);
    DumpStmt(TTryExceptStmt(AStmt).TryBody);
    Dec(IndentLevel);
    if TTryExceptStmt(AStmt).Handlers.Count > 0 then
    begin
      Line('Handlers:');
      Inc(IndentLevel);
      for I := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
      begin
        Line('on ' + TExceptHandlerClause(TTryExceptStmt(AStmt).Handlers.Items[I]).TypeName + ':');
        Inc(IndentLevel);
        DumpStmt(TExceptHandlerClause(TTryExceptStmt(AStmt).Handlers.Items[I]).Body);
        Dec(IndentLevel);
      end;
      Dec(IndentLevel);
    end;
    if TTryExceptStmt(AStmt).ExceptBody <> nil then
    begin
      Line('Except:');
      Inc(IndentLevel);
      DumpStmt(TTryExceptStmt(AStmt).ExceptBody);
      Dec(IndentLevel);
    end;
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TCaseStmt then
  begin
    Line('Case');
    Inc(IndentLevel);
    Line('Expr:');
    Inc(IndentLevel);
    DumpExpr(TCaseStmt(AStmt).Selector);
    Dec(IndentLevel);
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
    begin
      Line('Branch:');
      Inc(IndentLevel);
      DumpStmt(TASTStmt(TCaseStmt(AStmt).Branches.Items[I]));
      Dec(IndentLevel);
    end;
    if TCaseStmt(AStmt).ElseStmt <> nil then
    begin
      Line('Else:');
      Inc(IndentLevel);
      DumpStmt(TCaseStmt(AStmt).ElseStmt);
      Dec(IndentLevel);
    end;
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TStaticSubscriptAssign then
  begin
    Line('SubscriptAssign(' + TStaticSubscriptAssign(AStmt).ArrayName + ')');
    Inc(IndentLevel);
    Line('Index:');
    Inc(IndentLevel);
    DumpExpr(TStaticSubscriptAssign(AStmt).IndexExpr);
    Dec(IndentLevel);
    Line('Value:');
    Inc(IndentLevel);
    DumpExpr(TStaticSubscriptAssign(AStmt).ValueExpr);
    Dec(IndentLevel);
    Dec(IndentLevel);
    Exit;
  end;

  if AStmt is TPointerWriteStmt then
  begin
    Line('PointerWrite');
    Inc(IndentLevel);
    DumpExpr(TPointerWriteStmt(AStmt).PtrExpr);
    DumpExpr(TPointerWriteStmt(AStmt).ValExpr);
    Dec(IndentLevel);
    Exit;
  end;

  Line(AStmt.ClassName);
end;

procedure DumpMethodDecl(ADecl: TMethodDecl);
var
  I: Integer;
  Flags: string;
begin
  Flags := '';
  if ADecl.IsVirtual then Flags := Flags + ' virtual';
  if ADecl.IsOverride then Flags := Flags + ' override';
  if ADecl.IsAbstract then Flags := Flags + ' abstract';
  if ADecl.IsOverload then Flags := Flags + ' overload';
  if ADecl.IsExternal then Flags := Flags + ' external(' + ADecl.ExternalName + ')';
  if ADecl.IsRecordMethod then Flags := Flags + ' record-method';
  if ADecl.VTableSlot >= 0 then Flags := Flags + ' vtable=' + IntToStr(ADecl.VTableSlot);
  if ADecl.IsInlineCandidate then Flags := Flags + ' inline-candidate';
  if ADecl.OwnerTypeName <> '' then
    Line('Method ' + ADecl.OwnerTypeName + '.' + ADecl.Name + Flags)
  else if ADecl.ReturnTypeName <> '' then
    Line('Function ' + ADecl.Name + ': ' + ADecl.ReturnTypeName + Flags)
  else
    Line('Procedure ' + ADecl.Name + Flags);
  Inc(IndentLevel);
  if ADecl.Params.Count > 0 then
  begin
    Line('Params:');
    Inc(IndentLevel);
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      Flags := '';
      if TMethodParam(ADecl.Params.Items[I]).IsVarParam then Flags := Flags + 'var ';
      if TMethodParam(ADecl.Params.Items[I]).IsConstParam then Flags := Flags + 'const ';
      if TMethodParam(ADecl.Params.Items[I]).IsOutParam then Flags := Flags + 'out ';
      if TMethodParam(ADecl.Params.Items[I]).IsOpenArray then Flags := Flags + 'open-array ';
      Indent();
      Write(Flags + TMethodParam(ADecl.Params.Items[I]).ParamName + ': ' + TMethodParam(ADecl.Params.Items[I]).TypeName);
      if TMethodParam(ADecl.Params.Items[I]).ResolvedType <> nil then
        Write(' -> ' + TypeStr(TMethodParam(ADecl.Params.Items[I]).ResolvedType));
      WriteLn();
    end;
    Dec(IndentLevel);
  end;
  if ADecl.ResolvedReturnType <> nil then
    Line('Returns: ' + TypeStr(ADecl.ResolvedReturnType));
  if ADecl.Body <> nil then
  begin
    Line('Body:');
    Inc(IndentLevel);
    DumpBlock(ADecl.Body);
    Dec(IndentLevel);
  end;
  Dec(IndentLevel);
end;

procedure DumpBlock(ABlock: TBlock);
var
  I: Integer;
begin
  if ABlock = nil then
  begin
    Line('<nil-block>');
    Exit;
  end;
  if ABlock.ConstDecls.Count > 0 then
  begin
    Line('Constants:');
    Inc(IndentLevel);
    for I := 0 to ABlock.ConstDecls.Count - 1 do
    begin
      Indent();
      Write(TConstDecl(ABlock.ConstDecls.Items[I]).Name);
      if TConstDecl(ABlock.ConstDecls.Items[I]).TypeName <> '' then
        Write(': ' + TConstDecl(ABlock.ConstDecls.Items[I]).TypeName);
      if TConstDecl(ABlock.ConstDecls.Items[I]).IsString then
        Write(' = "' + TConstDecl(ABlock.ConstDecls.Items[I]).StrVal + '"')
      else if TConstDecl(ABlock.ConstDecls.Items[I]).IsFloat then
        Write(' = ' + TConstDecl(ABlock.ConstDecls.Items[I]).StrVal)
      else
        Write(' = ' + IntToStr(TConstDecl(ABlock.ConstDecls.Items[I]).IntVal));
      WriteLn();
    end;
    Dec(IndentLevel);
  end;
  if ABlock.Decls.Count > 0 then
  begin
    Line('Vars:');
    Inc(IndentLevel);
    for I := 0 to ABlock.Decls.Count - 1 do
    begin
      Indent();
      Write(TVarDecl(ABlock.Decls.Items[I]).Names.Strings[0] + ': ' + TVarDecl(ABlock.Decls.Items[I]).TypeName);
      if TVarDecl(ABlock.Decls.Items[I]).ResolvedType <> nil then
        Write(' -> ' + TypeStr(TVarDecl(ABlock.Decls.Items[I]).ResolvedType));
      WriteLn();
    end;
    Dec(IndentLevel);
  end;
  if ABlock.ProcDecls.Count > 0 then
  begin
    for I := 0 to ABlock.ProcDecls.Count - 1 do
      DumpMethodDecl(TMethodDecl(ABlock.ProcDecls.Items[I]));
  end;
  if ABlock.Stmts.Count > 0 then
  begin
    Line('Stmts:');
    Inc(IndentLevel);
    for I := 0 to ABlock.Stmts.Count - 1 do
      DumpStmt(TASTStmt(ABlock.Stmts.Items[I]));
    Dec(IndentLevel);
  end;
end;

procedure DumpProgram(AProg: TProgram);
begin
  IndentLevel := 0;
  WriteLn('=== AST Dump: program ' + AProg.Name + ' ===');
  Inc(IndentLevel);
  if AProg.UsedUnits.Count > 0 then
  begin
    Line('Uses: ' + AProg.UsedUnits.Text);
  end;
  DumpBlock(AProg.Block);
  Dec(IndentLevel);
  WriteLn('=== End AST Dump ===');
end;

procedure DumpUnit(AUnit: TUnit);
begin
  IndentLevel := 0;
  WriteLn('=== AST Dump: unit ' + AUnit.Name + ' ===');
  Inc(IndentLevel);
  if AUnit.IntfBlock <> nil then
  begin
    Line('Interface:');
    Inc(IndentLevel);
    DumpBlock(AUnit.IntfBlock);
    Dec(IndentLevel);
  end;
  if AUnit.ImplBlock <> nil then
  begin
    Line('Implementation:');
    Inc(IndentLevel);
    DumpBlock(AUnit.ImplBlock);
    Dec(IndentLevel);
  end;
  Dec(IndentLevel);
  WriteLn('=== End AST Dump ===');
end;

end.
