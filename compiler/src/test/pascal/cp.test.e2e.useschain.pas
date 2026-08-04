{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.useschain;

{ Regression tests for the per-unit visibility / uses-chain lookup.

  - The implicit System unit must always be reachable without an
    explicit `uses` clause in the user program.
  - Builtins like WriteLn, IntToStr, Length must resolve through the
    chain, not via a special-cased compiler hook. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EUsesChainTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ImplicitSystem_NoUsesClause_WriteLnInt;
    procedure TestRun_ImplicitSystem_NoUsesClause_IntToStr;
    procedure TestRun_ImplicitSystem_NoUsesClause_Length;
    { Unit-qualified symbol references 'UnitName.Symbol'. }
    procedure TestRun_QualifiedSystem_CallExprAndStmt;
    procedure TestRun_QualifiedUnit_CallAndVar;
    procedure TestRun_DottedQualifiedUnit_CallAndVar;
    { Cross-unit const shadowing: two used units export the same const name;
      the unit later in the `uses` clause wins (last-in-uses), and reversing
      the order flips the winner. }
    procedure TestRun_CrossUnitConst_LastWins;
    procedure TestRun_CrossUnitConst_LastWins_Reversed;
    { Unit-qualified const disambiguation: a 'Unit.Foo' reference resolves
      against that specific unit's exports, so it is never shadowed by a
      same-named const in another used unit, regardless of `uses` order. }
    procedure TestRun_CrossUnitConst_QualifiedDisambig;
    { Unit-qualified ancestor in a class declaration: class(Unit.TParent)
      binds to that unit's type so inheritance works across units. }
    procedure TestRun_QualifiedInheritance;
    { Two units each declare an impl-private global of the SAME name; with
      unit-prefix mangling on module-scope globals they no longer collide at
      link, so a program using both links and runs. }
    procedure TestRun_SameNamedGlobals_NoLinkCollision;
    { Cross-unit interface VAR shadowing: two used units export the same var
      name; the unit later in `uses` wins a bare reference (last-in-uses), and
      reversing the order flips the winner — mirrors the const last-wins rule. }
    procedure TestRun_CrossUnitVar_LastWins;
    procedure TestRun_CrossUnitVar_LastWins_Reversed;
    { Unit-qualified VAR disambiguation: 'Unit.V' references that specific
      unit's own slot (distinct storage), independent of the bare last-wins
      winner, so both values are readable side by side. }
    procedure TestRun_CrossUnitVar_QualifiedDisambig;
    { Cross-unit TYPE shadowing: two used units export a class of the same name;
      they coexist (no 'Duplicate type name' error, no link collision) and a
      bare reference binds to the unit later in `uses` (last-in-uses wins),
      flipping when the order is reversed — mirrors the const/var rule. }
    procedure TestRun_CrossUnitType_LastWins;
    procedure TestRun_CrossUnitType_LastWins_Reversed;
    { Unit-qualified TYPE disambiguation: 'Unit.TShape' binds to that unit's own
      class (distinct vtable/dispatch), independent of the bare last-wins
      winner, so both behaviours are observable side by side. }
    procedure TestRun_CrossUnitType_QualifiedDisambig;
    { Unit-qualified ENUM member 'Unit.TEnum.Member' (field-access form) binds
      the enum type to that specific unit's exports via directed lookup, so it
      reaches members the bare/last-wins enum type does not — independent of
      `uses` order. }
    procedure TestRun_CrossUnitEnum_QualifiedMember;

    { Interface satisfied by a NON-VIRTUAL method inherited across units }
    procedure TestRun_CrossUnitIntf_InheritedNonVirtual;
    procedure TestRun_CrossUnitIntf_InheritedCasingMismatch;
    procedure TestRun_CrossUnitIntf_InheritedVirtualStillUsesVTable;
    procedure TestRun_CrossUnitIntf_OverrideWins;
    { Same shapes on the QBE backend, whose unit path emitted no itab at all }
    procedure TestRun_CrossUnitIntf_QBE_DerivedGetsOwnItab;
    procedure TestRun_CrossUnitIntf_QBE_MultiHopAndIntfAncestor;
  end;

implementation

procedure TE2EUsesChainTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-useschain');
end;

const
  LE = #10;

  SrcWriteLnInt = '''
    program P;
    begin
      WriteLn(42)
    end.
    ''';

  SrcIntToStr = '''
    program P;
    var
      S: string;
    begin
      S := IntToStr(123);
      WriteLn(S)
    end.
    ''';

  SrcLength = '''
    program P;
    var
      S: string;
      N: Integer;
    begin
      S := 'hello';
      N := Length(S);
      WriteLn(N)
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_WriteLnInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcWriteLnInt, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('writeln(42)', '42' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_IntToStr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcIntToStr, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('IntToStr(123)', '123' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcLength, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(''hello'')', '5' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_QualifiedSystem_CallExprAndStmt;
const
  Src = '''
    program P;
    begin
      System.WriteLn(System.Length('hello'))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 'System.WriteLn' (qualified call statement) and 'System.Length(...)'
    (qualified call expression) both resolve via the implicit System unit. }
  AssertTrue(CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(''hello'') = 5', '5' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_QualifiedUnit_CallAndVar;
const
  UnitSrc = '''
    unit qsym;
    interface
    function Add3(N: Integer): Integer;
    var
      GBase: Integer;
    implementation
    function Add3(N: Integer): Integer;
    begin
      Result := N + 3
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses qsym;
    begin
      qsym.GBase := 10;
      WriteLn(qsym.Add3(qsym.GBase))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Qualified assignment target (qsym.GBase :=), qualified var read
    (qsym.GBase), and qualified function call (qsym.Add3) across a used unit. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('qsym', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Add3(10) = 13', '13' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_DottedQualifiedUnit_CallAndVar;
const
  UnitSrc = '''
    unit My.Pkg;
    interface
    function Add3(N: Integer): Integer;
    var
      GBase: Integer;
    implementation
    function Add3(N: Integer): Integer;
    begin
      Result := N + 3
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses My.Pkg;
    begin
      My.Pkg.GBase := 10;
      WriteLn(My.Pkg.Add3(My.Pkg.GBase))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Same as above but through a two-part dotted unit name 'My.Pkg'. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('My.Pkg', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Add3(10) = 13', '13' + LE, Output);
end;

const
  UA_Const = '''
    unit ua;
    interface
    const Foo = 100;
    implementation
    end.
    ''';
  UB_Const = '''
    unit ub;
    interface
    const Foo = 200;
    implementation
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_LastWins;
const
  DrvSrc = '''
    program P;
    uses ua, ub;
    begin
      WriteLn(Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both ua and ub export `Foo`; ub is later in `uses`, so bare Foo = 200. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (ub) wins', '200' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_LastWins_Reversed;
const
  DrvSrc = '''
    program P;
    uses ub, ua;
    begin
      WriteLn(Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Reversed `uses` order: ua is now later, so bare Foo = 100. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (ua) wins', '100' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_QualifiedDisambig;
const
  DrvSrc = '''
    program P;
    uses ua, ub;
    begin
      WriteLn(ua.Foo);
      WriteLn(ub.Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both ua and ub export `Foo`; qualified references pick each unit's own
    value (ua.Foo = 100, ub.Foo = 200) independent of the bare last-wins rule. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('ua.Foo then ub.Foo', '100' + LE + '200' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_QualifiedInheritance;
const
  UnitSrc = '''
    unit ua;
    interface
    type
      TParent = class
        function Base: Integer;
      end;
    implementation
    function TParent.Base: Integer;
    begin
      Result := 41
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses ua;
    type
      TChild = class(ua.TParent)
        function Plus1: Integer;
      end;
    function TChild.Plus1: Integer;
    begin
      Result := Base() + 1
    end;
    var
      C: TChild;
    begin
      C := TChild.Create();
      WriteLn(C.Plus1())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { class(ua.TParent) resolves the qualified ancestor to ua's type; the child
    inherits Base (41) and adds 1 -> 42. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('ua', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('inherited Base + 1', '42' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_SameNamedGlobals_NoLinkCollision;
const
  UnitOne = '''
    unit uone;
    interface
    function GetOne: Integer;
    implementation
    var G: Integer;
    function GetOne: Integer;
    begin
      G := 11;
      Result := G
    end;
    end.
    ''';
  UnitTwo = '''
    unit utwo;
    interface
    function GetTwo: Integer;
    implementation
    var G: Integer;
    function GetTwo: Integer;
    begin
      G := 22;
      Result := G
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses uone, utwo;
    begin
      WriteLn(GetOne() + GetTwo())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both units emit a global named G; without unit-prefix mangling the two
    '$G' definitions collide at link.  Mangling makes them distinct, so the
    program links and prints 11 + 22 = 33. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UnitOne, UnitTwo, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('GetOne + GetTwo', '33' + LE, Output);
end;

const
  UVA_Var = '''
    unit uva;
    interface
    var V: Integer = 7;
    implementation
    end.
    ''';
  UVB_Var = '''
    unit uvb;
    interface
    var V: Integer = 9;
    implementation
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_CrossUnitVar_LastWins;
const
  DrvSrc = '''
    program P;
    uses uva, uvb;
    begin
      WriteLn(V)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both uva and uvb export `V`; uvb is later in `uses`, so bare V = 9.
    The shadowed uva.V keeps its own slot (no link collision). }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UVA_Var, UVB_Var, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (uvb) wins', '9' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitVar_LastWins_Reversed;
const
  DrvSrc = '''
    program P;
    uses uvb, uva;
    begin
      WriteLn(V)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Reversed `uses` order: uva is now later, so bare V = 7. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UVA_Var, UVB_Var, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (uva) wins', '7' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitVar_QualifiedDisambig;
const
  DrvSrc = '''
    program P;
    uses uva, uvb;
    begin
      WriteLn(uva.V);
      WriteLn(uvb.V)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Qualified references pick each unit's own slot (uva.V = 7, uvb.V = 9)
    regardless of the bare last-wins rule — distinct storage per unit. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UVA_Var, UVB_Var, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('uva.V then uvb.V', '7' + LE + '9' + LE, Output);
end;

const
  TCA_Type = '''
    unit tca;
    interface
    type
      TShape = class
        function Sides: Integer;
      end;
    implementation
    function TShape.Sides: Integer;
    begin
      Result := 3
    end;
    end.
    ''';
  TCB_Type = '''
    unit tcb;
    interface
    type
      TShape = class
        function Sides: Integer;
      end;
    implementation
    function TShape.Sides: Integer;
    begin
      Result := 4
    end;
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_CrossUnitType_LastWins;
const
  DrvSrc = '''
    program P;
    uses tca, tcb;
    var S: TShape;
    begin
      S := TShape.Create();
      WriteLn(S.Sides())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both tca and tcb export class `TShape`; tcb is later in `uses`, so bare
    TShape binds to tcb (Sides = 4).  The two types coexist with distinct
    code symbols — no duplicate-identifier error and no link collision. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(TCA_Type, TCB_Type, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (tcb) wins', '4' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitType_LastWins_Reversed;
const
  DrvSrc = '''
    program P;
    uses tcb, tca;
    var S: TShape;
    begin
      S := TShape.Create();
      WriteLn(S.Sides())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Reversed `uses` order: tca is now later, so bare TShape binds to tca
    (Sides = 3). }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(TCA_Type, TCB_Type, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (tca) wins', '3' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitType_QualifiedDisambig;
const
  DrvSrc = '''
    program P;
    uses tca, tcb;
    var
      A: tca.TShape;
      B: tcb.TShape;
    begin
      A := tca.TShape.Create();
      B := tcb.TShape.Create();
      WriteLn(A.Sides());
      WriteLn(B.Sides())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Qualified references bind each variable to its own unit's class, so
    A.Sides = 3 (tca) and B.Sides = 4 (tcb) regardless of last-wins. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(TCA_Type, TCB_Type, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('tca.TShape then tcb.TShape', '3' + LE + '4' + LE, Output);
end;

const
  EA_Enum = '''
    unit ea;
    interface
    type TPalette = (paOne, paTwo, paThree);
    implementation
    end.
    ''';
  EB_Enum = '''
    unit eb;
    interface
    type TPalette = (paZero, paOne);
    implementation
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_CrossUnitEnum_QualifiedMember;
const
  { ea.TPalette.paThree exists only in ea (ordinal 2); eb.TPalette.paZero only
    in eb (ordinal 0).  A flat/last-wins enum-type lookup would resolve one of
    them to the other unit's TPalette and fail "no member"; the qualifier picks
    each unit's own enum. }
  DrvSrc = '''
    program P;
    uses ea, eb;
    begin
      WriteLn(Ord(ea.TPalette.paThree));
      WriteLn(Ord(eb.TPalette.paZero))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(EA_Enum, EB_Enum, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('ea.paThree=2, eb.paZero=0', '2' + LE + '0' + LE, Output);
end;

{ ------------------------------------------------------------------ }
{ Interface method inherited across a unit boundary                     }
{ ------------------------------------------------------------------ }

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_InheritedNonVirtual;
var
  Output: string; RCode: Integer; Dir: string;
begin
  { ub.TDer satisfies IThing purely by inheriting ua.TBase.Id, which is
    NON-VIRTUAL and therefore has no vtable slot.  The itab emitted for TDer
    used to name TDer_Id -- a symbol nothing defines, because the body was
    emitted as ua_TBase_Id -- so the program linked and then died at load
    with "undefined symbol: TDer_Id".  The backends now climb the type
    DESCRIPTOR chain (populated across units) to the declaring ancestor. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := '/tmp/blaise-useschain-intf-inheritednonvirtual';
  if not DirectoryExists(Dir) then ForceDirectories(Dir);
  WriteFile(Dir + '/ua.pas',
    '''
unit ua;
    interface
    type
      IThing = interface
        function Id: string;
      end;
      TBase = class(IThing)
        FId: string;
        function Id: string;
      end;
    implementation
    function TBase.Id: string; begin Result := FId end;
    end.
    ''');
  WriteFile(Dir + '/ub.pas',
    '''
unit ub;
    interface
    uses ua;
    type
      TDer = class(TBase)
        constructor Create;
      end;
    implementation
    constructor TDer.Create;
    begin
      inherited Create();
      FId := 'inherited-ok';
    end;
    end.
    ''');
  AssertTrue('compile+link+run',
    CompileAndRunNativeCLI(
    '''
program P;
    uses ua, ub;
    var T: TDer; I: IThing;
    begin
      T := TDer.Create();
      I := T;
      WriteLn(I.Id())
    end.
    ''', False, Dir, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'inherited-ok', Trim(Output));
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_InheritedCasingMismatch;
var
  Output: string; RCode: Integer; Dir: string;
begin
  { The interface declares Id; the class spells it ID.  Pascal identifiers are
    case-insensitive but LINK symbols are not, so the descriptor lookup has to
    fold case -- otherwise it misses and falls through to the error. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := '/tmp/blaise-useschain-intf-inheritedcasingmismatch';
  if not DirectoryExists(Dir) then ForceDirectories(Dir);
  WriteFile(Dir + '/ua.pas',
    '''
unit ua;
    interface
    type
      IThing = interface
        function Id: string;
      end;
      TBase = class(IThing)
        FId: string;
        function ID: string;
      end;
    implementation
    function TBase.ID: string; begin Result := FId end;
    end.
    ''');
  WriteFile(Dir + '/ub.pas',
    '''
unit ub;
    interface
    uses ua;
    type
      TDer = class(TBase)
        constructor Create;
      end;
    implementation
    constructor TDer.Create;
    begin
      inherited Create();
      FId := 'casing-ok';
    end;
    end.
    ''');
  AssertTrue('compile+link+run',
    CompileAndRunNativeCLI(
    '''
program P;
    uses ua, ub;
    var T: TDer; I: IThing;
    begin
      T := TDer.Create();
      I := T;
      WriteLn(I.Id())
    end.
    ''', False, Dir, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'casing-ok', Trim(Output));
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_InheritedVirtualStillUsesVTable;
var
  Output: string; RCode: Integer; Dir: string;
begin
  { Regression guard: a VIRTUAL inherited method must still resolve through the
    vtable's ImplName, not the new descriptor climb.  Both routes happen to
    name the same symbol here, so what this really pins is that the vtable arm
    still fires first and the change did not reorder resolution. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := '/tmp/blaise-useschain-intf-inheritedvirtualstillusesvtable';
  if not DirectoryExists(Dir) then ForceDirectories(Dir);
  WriteFile(Dir + '/ua.pas',
    '''
unit ua;
    interface
    type
      IThing = interface
        function Id: string;
      end;
      TBase = class(IThing)
        FId: string;
        function Id: string; virtual;
      end;
    implementation
    function TBase.Id: string; begin Result := FId end;
    end.
    ''');
  WriteFile(Dir + '/ub.pas',
    '''
unit ub;
    interface
    uses ua;
    type
      TDer = class(TBase)
        constructor Create;
      end;
    implementation
    constructor TDer.Create;
    begin
      inherited Create();
      FId := 'virtual-ok';
    end;
    end.
    ''');
  AssertTrue('compile+link+run',
    CompileAndRunNativeCLI(
    '''
program P;
    uses ua, ub;
    var T: TDer; I: IThing;
    begin
      T := TDer.Create();
      I := T;
      WriteLn(I.Id())
    end.
    ''', False, Dir, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'virtual-ok', Trim(Output));
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_OverrideWins;
var
  Output: string; RCode: Integer; Dir: string;
begin
  { An OVERRIDE in the descendant must win over the ancestor's body.  A climb
    that searched the chain before consulting the vtable would wrongly pick the
    ancestor, so this pins the ordering from the other side. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := '/tmp/blaise-useschain-intf-overridewins';
  if not DirectoryExists(Dir) then ForceDirectories(Dir);
  WriteFile(Dir + '/ua.pas',
    '''
unit ua;
    interface
    type
      IThing = interface
        function Id: string;
      end;
      TBase = class(IThing)
        FId: string;
        function Id: string; virtual;
      end;
    implementation
    function TBase.Id: string; begin Result := 'BASE' end;
    end.
    ''');
  WriteFile(Dir + '/ub.pas',
    '''
unit ub;
    interface
    uses ua;
    type
      TDer = class(TBase)
        constructor Create;
        function Id: string; override;
      end;
    implementation
    constructor TDer.Create;
    begin
      inherited Create();
      FId := 'x';
    end;
    function TDer.Id: string; begin Result := 'DERIVED' end;
    end.
    ''');
  AssertTrue('compile+link+run',
    CompileAndRunNativeCLI(
    '''
program P;
    uses ua, ub;
    var T: TDer; I: IThing;
    begin
      T := TDer.Create();
      I := T;
      WriteLn(I.Id())
    end.
    ''', False, Dir, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'DERIVED', Trim(Output));
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_QBE_DerivedGetsOwnItab;
var
  Output: string; RCode: Integer;
begin
  { QBE's UNIT path (AppendUnit) skipped any class whose own ImplementsCount
    was 0, so a derived class that INHERITS its interface emitted no itab and
    no impllist at all -- the reference from the narrowing site then dangled:
      undefined reference to `itab_qb_TDer_IThing'
    The whole-program path (EmitInterfaceDefs) had always walked the ancestor
    chain; only the unit path lacked it, so single-unit tests never saw this.
    Native was unaffected -- which is why the native tests above passed. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(
    '''
unit qa;
    interface
    type
      IThing = interface
        function Id: string;
      end;
      TBase = class(IThing)
        FId: string;
        function Id: string;
      end;
    implementation
    function TBase.Id: string; begin Result := FId end;
    end.
    ''',
    '''
unit qb;
    interface
    uses qa;
    type
      TDer = class(TBase)
        constructor Create;
      end;
    implementation
    constructor TDer.Create;
    begin
      inherited Create();
      FId := 'derived-qbe-ok';
    end;
    end.
    ''',
    '''
program P;
    uses qa, qb;
    var T: TDer; I: IThing;
    begin
      T := TDer.Create();
      I := T;
      WriteLn(I.Id())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'derived-qbe-ok', Trim(Output));
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitIntf_QBE_MultiHopAndIntfAncestor;
var
  Output: string; RCode: Integer;
begin
  { Harder shape for the same QBE unit path, all in one program:
      * TLeaf reaches its interface through a PASS-THROUGH ancestor (TMid
        declares nothing), so a one-hop-only walk would miss it;
      * IDog descends from IAnimal, so narrowing to the ANCESTOR interface
        needs its own itab too (the interface parent chain);
      * Virt is overridden in TLeaf, so the vtable must still win over the
        descriptor-chain fallback. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(
    '''
unit ra;
    interface
    type
      IAnimal = interface
        function Name: string;
      end;
      IDog = interface(IAnimal)
        function Bark: string;
      end;
      TBase = class(IDog)
        function Name: string;
        function Bark: string;
        function Virt: string; virtual;
      end;
    implementation
    function TBase.Name: string; begin Result := 'base-name' end;
    function TBase.Bark: string; begin Result := 'woof' end;
    function TBase.Virt: string; begin Result := 'base-virt' end;
    end.
    ''',
    '''
unit rb;
    interface
    uses ra;
    type
      TMid = class(TBase)
      end;
      TLeaf = class(TMid)
        function Virt: string; override;
      end;
    implementation
    function TLeaf.Virt: string; begin Result := 'leaf-virt' end;
    end.
    ''',
    '''
program P;
    uses ra, rb;
    var L: TLeaf; D: IDog; A: IAnimal;
    begin
      L := TLeaf.Create();
      D := L;  A := L;
      WriteLn(D.Name(), '|', D.Bark(), '|', A.Name(), '|', L.Virt())
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('output', 'base-name|woof|base-name|leaf-virt', Trim(Output));
end;

initialization
  RegisterTest(TE2EUsesChainTests);

end.
