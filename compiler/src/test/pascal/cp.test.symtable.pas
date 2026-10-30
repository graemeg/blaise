{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.symtable;

interface

uses
  SysUtils, Classes,
  blaise.testing,
  uSymbolTable;

type
  TSymbolTableTests = class(TTestCase)
  published
    { Built-in primitive types are pre-registered }
    procedure TestBuiltin_Type_Integer;
    procedure TestBuiltin_Type_Int64;
    procedure TestBuiltin_Type_UInt32;
    procedure TestBuiltin_Type_Byte;
    procedure TestBuiltin_Type_Boolean;
    procedure TestBuiltin_Type_String;

    { Type descriptor properties }
    procedure TestTypeDesc_Integer_IsNumeric;
    procedure TestTypeDesc_Boolean_IsNotNumeric;
    procedure TestTypeDesc_String_IsString;
    procedure TestTypeDesc_Integer_IsNotString;

    { FindType is case-insensitive (Pascal identifiers are) }
    procedure TestFindType_CaseInsensitive;
    procedure TestFindType_Unknown_ReturnsNil;

    { Symbol definition }
    procedure TestDefine_Variable;
    procedure TestDefine_Procedure;
    procedure TestDefine_DuplicateInSameScope_ReturnsFalse;
    procedure TestDefine_SameNameDiffScope_IsAllowed;

    { Symbol lookup }
    procedure TestLookup_FindsInCurrentScope;
    procedure TestLookup_NotFound_ReturnsNil;
    procedure TestLookup_CaseInsensitive;

    { Scope nesting }
    procedure TestScope_InnerSeesOuter;
    procedure TestScope_OuterCannotSeeInner;
    procedure TestScope_InnerShadowsOuter;
    procedure TestScope_AfterPop_InnerSymbolsGone;
    procedure TestScope_DepthAfterPushPop;

    { Built-in procedures }
    procedure TestBuiltin_WriteLn_Exists;
    procedure TestBuiltin_Write_Exists;
    procedure TestBuiltin_WriteLn_IsProcedure;

    { Symbol properties }
    procedure TestSymbol_Variable_HasType;
    procedure TestSymbol_Procedure_HasVoidReturn;

    { Per-thread lookup context (TSymbolTableView) }
    procedure TestThreadView_SeededAndPrivateToTheThread;
    procedure TestThreadView_ConcurrentWorkersEachSeeTheirOwnUnit;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function MakeVar(const AName: string; AType: TTypeDesc): TSymbol;
begin
  Result := TSymbol.Create(AName, skVariable, AType);
end;

function MakeProc(const AName: string): TSymbol;
begin
  Result := TSymbol.Create(AName, skProcedure, nil);
end;

{ ------------------------------------------------------------------ }
{ Built-in types                                                      }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestBuiltin_Type_Integer;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('Integer type', ST.FindType('Integer'));
    AssertEquals('Integer kind', Ord(tyInteger), Ord(ST.FindType('Integer').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Type_Int64;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('Int64 type', ST.FindType('Int64'));
    AssertEquals('Int64 kind', Ord(tyInt64), Ord(ST.FindType('Int64').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Type_UInt32;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('UInt32 type', ST.FindType('UInt32'));
    AssertEquals('UInt32 kind', Ord(tyUInt32), Ord(ST.FindType('UInt32').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Type_Byte;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('Byte type', ST.FindType('Byte'));
    AssertEquals('Byte kind', Ord(tyByte), Ord(ST.FindType('Byte').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Type_Boolean;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('Boolean type', ST.FindType('Boolean'));
    AssertEquals('Boolean kind', Ord(tyBoolean), Ord(ST.FindType('Boolean').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Type_String;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('string type', ST.FindType('string'));
    AssertEquals('string kind', Ord(tyString), Ord(ST.FindType('string').Kind));
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Type descriptor properties                                          }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestTypeDesc_Integer_IsNumeric;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertTrue('Integer is numeric', ST.FindType('Integer').IsNumeric());
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestTypeDesc_Boolean_IsNotNumeric;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertFalse('Boolean is not numeric', ST.FindType('Boolean').IsNumeric());
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestTypeDesc_String_IsString;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertTrue('string IsString', ST.FindType('string').IsString());
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestTypeDesc_Integer_IsNotString;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertFalse('Integer IsString', ST.FindType('Integer').IsString());
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ FindType                                                            }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestFindType_CaseInsensitive;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('integer lowercase', ST.FindType('integer'));
    AssertNotNull('INTEGER uppercase', ST.FindType('INTEGER'));
    AssertNotNull('String mixed',      ST.FindType('String'));
    AssertSame('Same descriptor', ST.FindType('Integer'), ST.FindType('integer'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestFindType_Unknown_ReturnsNil;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNull('unknown type', ST.FindType('Foobar'));
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Symbol definition                                                   }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestDefine_Variable;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeVar('x', ST.FindType('Integer'));
    AssertTrue('Define succeeds', ST.Define(Sym));
    AssertSame('Lookup finds it', Sym, ST.Lookup('x'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestDefine_Procedure;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeProc('Greet');
    AssertTrue('Define succeeds', ST.Define(Sym));
    AssertEquals('Kind', Ord(skProcedure), Ord(ST.Lookup('Greet').Kind));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestDefine_DuplicateInSameScope_ReturnsFalse;
var
  ST: TSymbolTable;
  S1, S2: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    S1 := MakeVar('x', ST.FindType('Integer'));
    S2 := MakeVar('x', ST.FindType('string'));
    AssertTrue('First define ok', ST.Define(S1));
    AssertFalse('Duplicate fails', ST.Define(S2));
    S2.Free();
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestDefine_SameNameDiffScope_IsAllowed;
var
  ST: TSymbolTable;
  S1, S2: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    S1 := MakeVar('n', ST.FindType('Integer'));
    AssertTrue('Outer define ok', ST.Define(S1));
    ST.PushScope();
    S2 := MakeVar('n', ST.FindType('string'));
    AssertTrue('Inner define ok — shadowing allowed', ST.Define(S2));
    ST.PopScope();
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Symbol lookup                                                       }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestLookup_FindsInCurrentScope;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeVar('result', ST.FindType('Integer'));
    ST.Define(Sym);
    AssertSame('Found', Sym, ST.Lookup('result'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestLookup_NotFound_ReturnsNil;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNull('Missing symbol', ST.Lookup('doesNotExist'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestLookup_CaseInsensitive;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeVar('MyVar', ST.FindType('Integer'));
    ST.Define(Sym);
    AssertSame('lowercase', Sym, ST.Lookup('myvar'));
    AssertSame('uppercase', Sym, ST.Lookup('MYVAR'));
    AssertSame('mixed',     Sym, ST.Lookup('MyVar'));
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Scope nesting                                                       }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestScope_InnerSeesOuter;
var
  ST:    TSymbolTable;
  Outer: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Outer := MakeVar('x', ST.FindType('Integer'));
    ST.Define(Outer);
    ST.PushScope();
    AssertSame('Inner sees outer x', Outer, ST.Lookup('x'));
    ST.PopScope();
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestScope_OuterCannotSeeInner;
var
  ST:    TSymbolTable;
  Inner: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    ST.PushScope();
    Inner := MakeVar('local', ST.FindType('Integer'));
    ST.Define(Inner);
    ST.PopScope();
    AssertNull('Outer cannot see inner local', ST.Lookup('local'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestScope_InnerShadowsOuter;
var
  ST:     TSymbolTable;
  Outer, Inner: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Outer := MakeVar('n', ST.FindType('Integer'));
    ST.Define(Outer);
    ST.PushScope();
    Inner := MakeVar('n', ST.FindType('string'));
    ST.Define(Inner);
    AssertSame('Inner n shadows outer n', Inner, ST.Lookup('n'));
    ST.PopScope();
    AssertSame('After pop, outer n visible again', Outer, ST.Lookup('n'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestScope_AfterPop_InnerSymbolsGone;
var
  ST:    TSymbolTable;
  Inner: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    ST.PushScope();
    Inner := MakeVar('temp', ST.FindType('Integer'));
    ST.Define(Inner);
    AssertNotNull('Present before pop', ST.Lookup('temp'));
    ST.PopScope();
    AssertNull('Gone after pop', ST.Lookup('temp'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestScope_DepthAfterPushPop;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertEquals('Depth 1 initially', 1, ST.ScopeDepth);
    ST.PushScope();
    AssertEquals('Depth 2 after push', 2, ST.ScopeDepth);
    ST.PushScope();
    AssertEquals('Depth 3', 3, ST.ScopeDepth);
    ST.PopScope();
    AssertEquals('Depth 2 after pop', 2, ST.ScopeDepth);
    ST.PopScope();
    AssertEquals('Depth 1 restored', 1, ST.ScopeDepth);
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Built-in procedures                                                 }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestBuiltin_WriteLn_Exists;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('WriteLn exists', ST.Lookup('WriteLn'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_Write_Exists;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertNotNull('Write exists', ST.Lookup('Write'));
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestBuiltin_WriteLn_IsProcedure;
var
  ST: TSymbolTable;
begin
  ST := TSymbolTable.Create();
  try
    AssertEquals('WriteLn kind',
      Ord(skProcedure), Ord(ST.Lookup('WriteLn').Kind));
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Symbol properties                                                   }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestSymbol_Variable_HasType;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeVar('s', ST.FindType('string'));
    ST.Define(Sym);
    AssertSame('TypeDesc', ST.FindType('string'), ST.Lookup('s').TypeDesc);
  finally
    ST.Free();
  end;
end;

procedure TSymbolTableTests.TestSymbol_Procedure_HasVoidReturn;
var
  ST:  TSymbolTable;
  Sym: TSymbol;
begin
  ST := TSymbolTable.Create();
  try
    Sym := MakeProc('DoSomething');
    ST.Define(Sym);
    AssertNull('Procedure has no return type', ST.Lookup('DoSomething').TypeDesc);
  finally
    ST.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Per-thread lookup context                                           }
{ ------------------------------------------------------------------ }

procedure TSymbolTableTests.TestThreadView_SeededAndPrivateToTheThread;
var
  ST: TSymbolTable;
  V: TSymbolTableView;
begin
  ST := TSymbolTable.Create();
  try
    ST.DefineOwningUnit := 'Main';
    ST.BypassUsesChain := False;
    V := ST.EnterThreadView();
    AssertEquals('view seeded from the table', 'Main', ST.DefineOwningUnit);
    ST.DefineOwningUnit := 'Worker';
    ST.BypassUsesChain := True;
    AssertEquals('write lands in the view', 'Worker', ST.DefineOwningUnit);
    AssertTrue('bypass write lands in the view', ST.BypassUsesChain);
    ST.LeaveThreadView();
    AssertEquals('table field untouched by the view', 'Main', ST.DefineOwningUnit);
    AssertFalse('table bypass untouched by the view', ST.BypassUsesChain);
    V := nil;
  finally
    ST.Free();
  end;
end;

type
  { One codegen worker's use of a shared table: re-point DefineOwningUnit at
    "its" unit and read it straight back, many times over. }
  TViewWorker = class(TThread)
  public
    Table: TSymbolTable;
    UnitName: string;
    Mismatches: Int;
  protected
    procedure Execute; override;
  end;

procedure TViewWorker.Execute;
var
  V: TSymbolTableView;
  I: Int;
begin
  V := Self.Table.EnterThreadView();
  try
    for I := 1 to 20000 do
    begin
      Self.Table.DefineOwningUnit := Self.UnitName;
      if Self.Table.DefineOwningUnit <> Self.UnitName then
        Inc(Self.Mismatches);
    end;
  finally
    Self.Table.LeaveThreadView();
  end;
end;

procedure TSymbolTableTests.TestThreadView_ConcurrentWorkersEachSeeTheirOwnUnit;
var
  ST: TSymbolTable;
  W: array[0..3] of TViewWorker;
  I, Total: Int;
begin
  { The incremental driver runs one worker per unit against ONE table.  With
    DefineOwningUnit a plain shared field, a worker read back another worker's
    unit -- and the racing string stores released old values twice. }
  ST := TSymbolTable.Create();
  try
    ST.DefineOwningUnit := 'Program';
    for I := 0 to 3 do
    begin
      W[I] := TViewWorker.Create(True);
      W[I].Table := ST;
      W[I].UnitName := 'unit' + IntToStr(I);   { a counted, heap string }
      W[I].Start();
    end;
    Total := 0;
    for I := 0 to 3 do
    begin
      W[I].WaitFor();
      Total := Total + W[I].Mismatches;
      W[I].Free();
    end;
    AssertEquals('reads of another worker''s unit', 0, Total);
    AssertEquals('table field untouched by the workers', 'Program',
      ST.DefineOwningUnit);
  finally
    ST.Free();
  end;
end;

initialization
  RegisterTest(TSymbolTableTests);

end.
