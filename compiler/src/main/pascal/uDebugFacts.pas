{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uDebugFacts;

{ Codegen-produced debug facts for the OPDF emitter.

  The OPDF emitter (uDebugOPDF) is an AST walk: on its own it can only GUESS
  runtime facts — frame offsets, statement addresses, function extents.  The
  native backend owns all of those exactly: it lays out every frame slot,
  prints every instruction, and can drop a local label at each statement.

  During native codegen (when --debug-opdf is on) the backend records one
  TDbgFunc per emitted function: the assembly symbol (LowPC), an end label
  emitted after the final ret (exact HighPC), every frame slot with its real
  %rbp offset, and a .Ldbg_N label per statement with its source line.  The
  OPDF emitter consumes these facts instead of guessing, and the resulting
  section is appended to the SAME assembly file, so the local labels resolve
  without exporting anything.

  The QBE backend cannot provide facts (QBE itself assigns frames and
  addresses), so its OPDF output keeps the approximate AST-walk behaviour. }

interface

uses
  Classes, contnrs, uSymbolTable;

type
  { One frame slot: a parameter or local with its resolved %rbp offset.
    Negative offsets are below the frame pointer (register-spilled params and
    locals); positive offsets are caller-pushed stack parameters. }
  TDbgVar = class
  public
    Name: string;
    [Unretained] TypeDesc: TTypeDesc;  { non-owned — symbol table pool }
    RbpOffset: Integer;
    IsParam: Boolean;
    IsVarParam: Boolean;
    IsConstParam: Boolean;
    { The slot holds the value's ADDRESS rather than the value itself
      (var/out params, by-reference aggregates, captured outer locals) —
      emitted as LocationExpr=3 'RBP-relative indirect'. }
    Indirect: Boolean;
    { Open-array parameter: the slot holds the data pointer (no heap header);
      the element count is High+1, where High lives in a separate companion
      stack slot at HighRbpOffset.  Emitted as LocationExpr=5 'open-array'
      with the companion offset trailing the LocationData. }
    IsOpenArray: Boolean;
    HighRbpOffset: Integer;
  end;

  { One statement-level line marker: the backend emitted LabelName ('.Ldbg_N')
    immediately before the statement's first instruction. }
  TDbgLine = class
  public
    LabelName: string;
    Line: Integer;
    Col: Integer;
  end;

  TDbgFunc = class
  public
    SymbolName: string;  { emitted assembly label — LowPC }
    EndLabel: string;    { label after the final ret — exact HighPC }
    SourceFile: string;  { .pas file the function's body lives in; empty
                           means the emitter falls back to the program's
                           main source file }
    Vars: TObjectList;   { owned TDbgVar }
    Lines: TObjectList;  { owned TDbgLine }
    constructor Create;
    function AddVar(const AName: string; AType: TTypeDesc;
                    AOffset: Integer): TDbgVar;
    function FindVar(const AName: string): TDbgVar;
  end;

  TDbgFacts = class
  public
    Funcs: TObjectList;  { owned TDbgFunc }
    constructor Create;
    function BeginFunc(const ASymbol: string): TDbgFunc;
  end;

implementation

uses SysUtils;

constructor TDbgFunc.Create;
begin
  inherited Create();
  Vars := TObjectList.Create(True);
  Lines := TObjectList.Create(True);
end;

function TDbgFunc.AddVar(const AName: string; AType: TTypeDesc;
  AOffset: Integer): TDbgVar;
begin
  Result := TDbgVar.Create();
  Result.Name := AName;
  Result.TypeDesc := AType;
  Result.RbpOffset := AOffset;
  Vars.Add(Result);
end;

function TDbgFunc.FindVar(const AName: string): TDbgVar;
var
  I: Integer;
begin
  for I := 0 to Vars.Count - 1 do
  begin
    Result := TDbgVar(Vars.Items[I]);
    if SameText(Result.Name, AName) then
      Exit;
  end;
  Result := nil;
end;

constructor TDbgFacts.Create;
begin
  inherited Create();
  Funcs := TObjectList.Create(True);
end;

function TDbgFacts.BeginFunc(const ASymbol: string): TDbgFunc;
begin
  Result := TDbgFunc.Create();
  Result.SymbolName := ASymbol;
  Funcs.Add(Result);
end;

end.
