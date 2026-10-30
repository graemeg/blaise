{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.multifile;

{ Tests for multi-file compilation: TUnitLoader (search, cycle detection,
  dependency ordering), TSemanticAnalyser.AnalyseUnitForExport (cross-unit
  symbol visibility), and combined code generation via AppendUnit/AppendProgram. }

interface

uses
  Classes, SysUtils, Contnrs, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  uUnitLoader;

type
  TMultifileTests = class(TTestCase)
  private
    FTmpDir: string;
    procedure WriteUnit(const AName, ASrc: string);
    function  MakeSearchPaths: TStringList;
    function  ParseProg(const ASrc: string): TProgram;
    function  ParseUnitSrc(const ASrc: string): TUnit;
    { Analyse AUnitSrcs (in dependency order) then AProgSrc in one analyser.
      Returns '' when analysis succeeds, else the semantic error message. }
    function  AnalyseUnitsAndProg(const AUnitSrcs: array of string;
                                  const AProgSrc: string): string;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { ------------------------------------------------------------------ }
    { TUnitLoader                                                          }
    { ------------------------------------------------------------------ }
    procedure TestUnitLoader_LocatesUnitInSearchPath;
    procedure TestUnitLoader_RaisesOnMissingUnit;
    procedure TestUnitLoader_DetectsCycle;
    procedure TestUnitLoader_ImplSectionBackEdge_Tolerated;
    procedure TestUnitLoader_DependencyOrder;
    { ------------------------------------------------------------------ }
    { AnalyseUnitForExport                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemanticAnalyser_ExportedTypeVisibleInProgram;
    procedure TestSemanticAnalyser_ExportedFuncVisibleInProgram;
    { Flat-merge of units that each privately bind the same external C symbol,
      or bind to a real RTL function — must not raise a false
      "ambiguous overload" / "duplicate identifier" (bugs.txt: runtime module
      library compile failed). }
    procedure TestSemanticAnalyser_DuplicateExternalBindingTolerated;
    procedure TestSemanticAnalyser_ExternalBindingToRealFuncTolerated;
    procedure TestSemanticAnalyser_PrivateImplProcsPerUnitNotAmbiguous;
    { A used unit privately binds an external C symbol in its IMPLEMENTATION
      section; the program then declares its OWN binding of the same name.
      The program's declaration must define a callable symbol.  It used to be
      swallowed: the program's forward/impl pairing searched FProcIndex — which
      is global across every compiled unit — without restricting the match to
      the current compilation, so the unit's private, body-less external entry
      looked like a forward declaration the program was implementing.  The
      program's own declaration was then skipped rather than defined, and the
      call reported "Undeclared function".  The unit-to-unit half of this was
      already fixed in AnalyseUnit; this is the program half.  Real-world bite:
      any program that binds a libc symbol async.io also binds privately (e.g.
      getsockopt) failed to compile. }
    procedure TestSemanticAnalyser_ProgramExternalShadowsUnitPrivateExternal;
    { ------------------------------------------------------------------ }
    { Uses-clause visibility (GH #248)                                     }
    { ------------------------------------------------------------------ }
    { A program sees only the units in its own uses clause.  A type, const,
      routine or variable of a unit that is merely used BY a used unit is not
      visible, bare or unit-qualified -- the same rule FPC and Delphi apply.
      Blaise resolved them through the flat global symbol table. }
    procedure TestUsesVisibility_TransitiveTypeRejected;
    procedure TestUsesVisibility_TransitiveQualifiedTypeRejected;
    procedure TestUsesVisibility_TransitiveRoutineRejected;
    procedure TestUsesVisibility_TransitiveConstRejected;
    { ...and as a generic type argument. }
    procedure TestUsesVisibility_TransitiveTypeArgRejected;
    procedure TestUsesVisibility_ImplUsesNotReExported;
    { A unit's implementation-section uses are visible to that unit's own
      implementation. }
    procedure TestUsesVisibility_ImplUsesVisibleInImplementation;
    { A transitive unit's type may still be USED without being named: through
      a variable, a function result, or an inherited member. }
    procedure TestUsesVisibility_TransitiveTypeReachedThroughValues;
    procedure TestUsesVisibility_InheritedFromTransitiveClass;
    { A generic body resolves names in its DECLARING unit's uses, so a
      consumer need not use those units itself. }
    procedure TestUsesVisibility_GenericBodySeesDeclaringUnitUses;
    procedure TestUsesVisibility_GenericFuncBodySeesDeclaringUnitUses;
    { ...while the consumer's own type arguments still resolve. }
    procedure TestUsesVisibility_GenericOverConsumerType;
    { A loaded unit that declares its own PInteger takes the flat slot; a
      program that does not use it still gets System's PInteger, and one that
      does gets the unit's. }
    procedure TestUsesVisibility_UnitShadowsSystemPointerAlias;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.SetUp;
begin
  FTmpDir := GetTempDir() + 'blaise_mf_' + IntToStr(GetProcessID());
  ForceDirectories(FTmpDir);
end;

procedure TMultifileTests.TearDown;
begin
  { Temp .pas files are left; just attempt to remove the dir. }
  RemoveDir(FTmpDir);
end;

procedure TMultifileTests.WriteUnit(const AName, ASrc: string);
var
  F: TStringList;
begin
  F := TStringList.Create();
  try
    F.Text := ASrc;
    F.SaveToFile(FTmpDir + '/' + AName + '.pas');
  finally
    F.Free();
  end;
end;

function TMultifileTests.MakeSearchPaths: TStringList;
begin
  Result := TStringList.Create();
  Result.Add(FTmpDir);
end;

function TMultifileTests.ParseProg(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TMultifileTests.ParseUnitSrc(const ASrc: string): TUnit;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
end;

function TMultifileTests.AnalyseUnitsAndProg(const AUnitSrcs: array of string;
                                             const AProgSrc: string): string;
var
  Units: TObjectList;
  Prog:  TProgram;
  SA:    TSemanticAnalyser;
  I:     Int;
begin
  Result := '';
  Units := TObjectList.Create(True);
  Prog  := nil;
  SA    := TSemanticAnalyser.Create();
  try
    try
      for I := 0 to High(AUnitSrcs) do
      begin
        Units.Add(ParseUnitSrc(AUnitSrcs[I]));
        SA.AnalyseUnitForExport(TUnit(Units.Items[Units.Count - 1]));
      end;
      Prog := ParseProg(AProgSrc);
      SA.Analyse(Prog);
    except
      on E: ESemanticError do
        Result := E.Message;
    end;
  finally
    SA.Free();
    Prog.Free();
    Units.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ TUnitLoader tests                                                    }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestUnitLoader_LocatesUnitInSearchPath;
const
  Src =
    '''
        unit MathUtils;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('MathUtils', Src);

  Paths  := MakeSearchPaths();
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create();
  try
    Names.Add('MathUtils');
    Units := Loader.LoadAll(Names);
    try
      AssertEquals('one unit loaded', 1, Units.Count);
      AssertEquals('unit name', 'MathUtils', TUnit(Units.Items[0]).Name);
    finally
      Units.Free();
    end;
  finally
    Names.Free();
    Loader.Free();
    Paths.Free();
  end;
end;

procedure TMultifileTests.TestUnitLoader_RaisesOnMissingUnit;
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  Paths  := MakeSearchPaths();
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create();
  try
    Names.Add('NoSuchUnit');
    try
      Units := Loader.LoadAll(Names);
      Units.Free();
      Fail('Expected EUnitNotFound');
    except
      on E: EUnitNotFound do ;  { expected }
    end;
  finally
    Names.Free();
    Loader.Free();
    Paths.Free();
  end;
end;

procedure TMultifileTests.TestUnitLoader_DetectsCycle;
const
  SrcA =
    '''
        unit CycleA;
        interface
        uses CycleB;
        implementation
        end.
        ''';
  SrcB =
    '''
        unit CycleB;
        interface
        uses CycleA;
        implementation
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('CycleA', SrcA);
  WriteUnit('CycleB', SrcB);

  Paths  := MakeSearchPaths();
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create();
  try
    Names.Add('CycleA');
    try
      Units := Loader.LoadAll(Names);
      Units.Free();
      Fail('Expected ECircularDependency');
    except
      on E: ECircularDependency do ;  { expected }
    end;
  finally
    Names.Free();
    Loader.Free();
    Paths.Free();
  end;
end;

procedure TMultifileTests.TestUnitLoader_ImplSectionBackEdge_Tolerated;
const
  { BackA's INTERFACE uses BackB; BackB's IMPLEMENTATION uses BackA.  This is a
    legal Object Pascal arrangement — interfaces are compiled before bodies, so
    BackB's body may name BackA even though BackA's interface (transitively)
    needs BackB.  It must load without an ECircularDependency, unlike the
    interface↔interface cycle above. }
  SrcA =
    '''
        unit BackA;
        interface
        uses BackB;
        implementation
        end.
        ''';
  SrcB =
    '''
        unit BackB;
        interface
        implementation
        uses BackA;
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('BackA', SrcA);
  WriteUnit('BackB', SrcB);

  Paths  := MakeSearchPaths();
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create();
  try
    Names.Add('BackA');
    { Must NOT raise — the back-edge is through an implementation-section use. }
    Units := Loader.LoadAll(Names);
    try
      AssertEquals('both units loaded', 2, Units.Count);
    finally
      Units.Free();
    end;
  finally
    Names.Free();
    Loader.Free();
    Paths.Free();
  end;
end;

procedure TMultifileTests.TestUnitLoader_DependencyOrder;
const
  SrcC =
    '''
        unit DepC;
        interface
        implementation
        end.
        ''';
  SrcB =
    '''
        unit DepB;
        interface
        uses DepC;
        implementation
        end.
        ''';
  SrcA =
    '''
        unit DepA;
        interface
        uses DepB;
        implementation
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('DepC', SrcC);
  WriteUnit('DepB', SrcB);
  WriteUnit('DepA', SrcA);

  Paths  := MakeSearchPaths();
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create();
  try
    Names.Add('DepA');
    Units := Loader.LoadAll(Names);
    try
      AssertEquals('three units loaded', 3, Units.Count);
      AssertEquals('first is leaf DepC', 'DepC', TUnit(Units.Items[0]).Name);
      AssertEquals('second is DepB',     'DepB', TUnit(Units.Items[1]).Name);
      AssertEquals('third is DepA',      'DepA', TUnit(Units.Items[2]).Name);
    finally
      Units.Free();
    end;
  finally
    Names.Free();
    Loader.Free();
    Paths.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ AnalyseUnitForExport tests                                           }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestSemanticAnalyser_ExportedTypeVisibleInProgram;
const
  UnitSrc =
    '''
        unit Shapes;
        interface
        type
          TPoint = record
            X: Integer;
            Y: Integer;
          end;
        implementation
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses Shapes;
        var p: TPoint;
        begin
          p.X := 1
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(U);
    { If TPoint is not in global scope, Analyse will raise ESemanticError }
    SA.Analyse(Prog);
    AssertNotNull('prog analysed', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_ExportedFuncVisibleInProgram;
const
  UnitSrc =
    '''
        unit MathU;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MathU;
        var r: Integer;
        begin
          r := Add(1, 2)
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_DuplicateExternalBindingTolerated;
const
  { Two units each declare the SAME parameterless external C binding in their
    implementation section and call it.  In the flat-merge both land in the
    one global overload group; they denote ONE function and must collapse. }
  UnitASrc =
    '''
        unit AltA;
        interface
        procedure DoA;
        implementation
        procedure ext_abort; external name 'abort';
        procedure DoA;
        begin
          ext_abort()
        end;
        end.
        ''';
  UnitBSrc =
    '''
        unit AltB;
        interface
        procedure DoB;
        implementation
        procedure ext_abort; external name 'abort';
        procedure DoB;
        begin
          ext_abort()
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses AltA, AltB;
        begin
          DoA(); DoB()
        end.
        ''';
var
  UA, UB: TUnit;
  Prog:   TProgram;
  SA:     TSemanticAnalyser;
begin
  UA   := ParseUnitSrc(UnitASrc);
  UB   := ParseUnitSrc(UnitBSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(UA);
    SA.AnalyseUnitForExport(UB);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed without ambiguity', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    UB.Free();
    UA.Free();
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_ExternalBindingToRealFuncTolerated;
const
  { An unmangled RTL-style unit (blaise_*) exports a real function whose link
    symbol is its bare name; a second unit binds to it via `external name`.
    The flat-merge sees one real def + one external binding for the same link
    symbol — must not be a duplicate identifier nor an ambiguous overload. }
  MemSrc =
    '''
        unit blaise_testmem;
        interface
        function _TestGetMem(Size: Integer): Pointer;
        implementation
        function _TestGetMem(Size: Integer): Pointer;
        begin
          Result := nil
        end;
        end.
        ''';
  UseSrc =
    '''
        unit UserU;
        interface
        function GrabMem: Pointer;
        implementation
        function _TestGetMem(Size: Integer): Pointer; external name '_TestGetMem';
        function GrabMem: Pointer;
        begin
          Result := _TestGetMem(8)
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses blaise_testmem, UserU;
        var p: Pointer;
        begin
          p := GrabMem()
        end.
        ''';
var
  UM, UU: TUnit;
  Prog:   TProgram;
  SA:     TSemanticAnalyser;
begin
  UM   := ParseUnitSrc(MemSrc);
  UU   := ParseUnitSrc(UseSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(UM);
    SA.AnalyseUnitForExport(UU);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed: external binding to real func', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    UU.Free();
    UM.Free();
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_PrivateImplProcsPerUnitNotAmbiguous;
const
  { Two units each declare a PRIVATE (implementation-only, non-external) helper
    of the same name and call it.  Each unit's call must bind to its own copy;
    the other unit's private helper is not a visible competing candidate. }
  UnitASrc =
    '''
        unit PrivA;
        interface
        function GoA: Integer;
        implementation
        function Helper(X: Integer): Integer;
        begin
          Result := X + 1
        end;
        function GoA: Integer;
        begin
          Result := Helper(10)
        end;
        end.
        ''';
  UnitBSrc =
    '''
        unit PrivB;
        interface
        function GoB: Integer;
        implementation
        function Helper(X: Integer): Integer;
        begin
          Result := X + 2
        end;
        function GoB: Integer;
        begin
          Result := Helper(20)
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses PrivA, PrivB;
        var r: Integer;
        begin
          r := GoA() + GoB()
        end.
        ''';
var
  UA, UB: TUnit;
  Prog:   TProgram;
  SA:     TSemanticAnalyser;
begin
  UA   := ParseUnitSrc(UnitASrc);
  UB   := ParseUnitSrc(UnitBSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(UA);
    SA.AnalyseUnitForExport(UB);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed: per-unit private helpers', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    UB.Free();
    UA.Free();
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_ProgramExternalShadowsUnitPrivateExternal;
const
  { The unit's ext_probe is implementation-private and body-less.  The program
    declares its own ext_probe and calls it — that call must resolve. }
  UnitSrc =
    '''
        unit ExtPriv;
        interface
        function GoX: Integer;
        implementation
        function ext_probe(X: Integer): Integer; external name 'abs';
        function GoX: Integer;
        begin
          Result := ext_probe(-7)
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses ExtPriv;
        function ext_probe(X: Integer): Integer; external name 'abs';
        var r: Integer;
        begin
          r := ext_probe(-5) + GoX()
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed: own external binding not swallowed by the '
      + 'used unit''s private one', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Uses-clause visibility (GH #248)                                     }
{ ------------------------------------------------------------------ }

const
  VisTypesSrc =
    '''
        unit VisTypes;
        interface
        type
          TUnitRec = record
            One: Integer;
            Two: Integer;
          end;
          TBaseObj = class
            function Hello(): Integer;
          end;
        const
          VisAnswer = 42;
        function VisTwice(N: Integer): Integer;
        implementation
        function TBaseObj.Hello(): Integer;
        begin
          Result := 7
        end;
        function VisTwice(N: Integer): Integer;
        begin
          Result := N * 2
        end;
        end.
        ''';
  VisBaseSrc =
    '''
        unit VisBase;
        interface
        uses VisTypes;
        type
          TDerivedObj = class(TBaseObj)
          end;
        var
          Ur: TUnitRec;
        function MakeRec(): TUnitRec;
        implementation
        function MakeRec(): TUnitRec;
        begin
          Result.One := 5
        end;
        end.
        ''';

procedure TMultifileTests.TestUsesVisibility_TransitiveTypeRejected;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          Ur: TUnitRec;
        begin
          Ur.One := 1
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc);
  AssertTrue('rejected, naming the type: ' + Msg, Pos('TUnitRec', Msg) >= 0);
  AssertTrue('names the unit to add to uses: ' + Msg,
    Pos('declared in unit ''VisTypes''', Msg) >= 0);
  AssertTrue('mentions the uses clause: ' + Msg,
    Pos('not in the uses clause', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_TransitiveQualifiedTypeRejected;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          R: VisTypes.TUnitRec;
        begin
          R.One := 1
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc);
  AssertTrue('qualified name of an unused unit rejected: ' + Msg,
    Pos('TUnitRec', Msg) >= 0);
  AssertTrue('names the unit to add: ' + Msg,
    Pos('''TUnitRec'' is declared in unit ''VisTypes''', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_TransitiveRoutineRejected;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          N: Integer;
        begin
          N := VisTwice(3)
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc);
  AssertTrue('routine of an unused unit rejected: ' + Msg,
    Pos('VisTwice', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_TransitiveConstRejected;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          N: Integer;
        begin
          N := VisAnswer
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc);
  AssertTrue('const of an unused unit rejected: ' + Msg,
    Pos('VisAnswer', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_ImplUsesNotReExported;
const
  MidSrc =
    '''
        unit VisMid;
        interface
        function MidValue(): Integer;
        implementation
        uses VisTypes;
        function MidValue(): Integer;
        begin
          Result := VisAnswer
        end;
        end.
        ''';
  ProgSrc =
    '''
        program P;
        uses VisMid;
        var
          N: Integer;
        begin
          N := MidValue() + VisTwice(1)
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, MidSrc], ProgSrc);
  AssertTrue('implementation uses are private to the unit: ' + Msg,
    Pos('VisTwice', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_ImplUsesVisibleInImplementation;
const
  MidSrc =
    '''
        unit VisMid;
        interface
        function MidValue(): Integer;
        implementation
        uses VisTypes;
        type
          TLocalBox = record
            R: TUnitRec;
          end;
        var
          Box: TLocalBox;
        function MidValue(): Integer;
        var
          O: TBaseObj;
        begin
          O := TBaseObj.Create();
          Box.R.One := VisTwice(VisAnswer);
          Result := Box.R.One + O.Hello()
        end;
        end.
        ''';
  ProgSrc =
    '''
        program P;
        uses VisMid;
        var
          N: Integer;
        begin
          N := MidValue()
        end.
        ''';
begin
  AssertEquals('implementation uses resolve inside the unit', '',
    AnalyseUnitsAndProg([VisTypesSrc, MidSrc], ProgSrc));
end;

procedure TMultifileTests.TestUsesVisibility_TransitiveTypeReachedThroughValues;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          N: Integer;
        begin
          Ur.One := 1;
          VisBase.Ur.Two := 2;
          N := MakeRec().One + Ur.Two
        end.
        ''';
begin
  AssertEquals('values of a transitive type need no uses entry', '',
    AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc));
end;

procedure TMultifileTests.TestUsesVisibility_InheritedFromTransitiveClass;
const
  ProgSrc =
    '''
        program P;
        uses VisBase;
        var
          D: TDerivedObj;
          N: Integer;
        begin
          D := TDerivedObj.Create();
          N := D.Hello()
        end.
        ''';
begin
  AssertEquals('inherited member of a transitive base class', '',
    AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc], ProgSrc));
end;

const
  VisHelpSrc =
    '''
        unit VisHelp;
        interface
        const
          HelpBase = 100;
        function HelpAdd(N: Integer): Integer;
        implementation
        function HelpAdd(N: Integer): Integer;
        begin
          Result := N + HelpBase
        end;
        end.
        ''';
  VisGenSrc =
    '''
        unit VisGen;
        interface
        uses VisHelp;
        type
          TGenBox<T> = class
            FValue: T;
            function Bumped(): Integer;
          end;
        function GenBump<T>(const A: T): Integer;
        implementation
        function TGenBox<T>.Bumped(): Integer;
        begin
          Result := HelpAdd(HelpBase)
        end;
        function GenBump<T>(const A: T): Integer;
        begin
          Result := HelpAdd(SizeOf(A))
        end;
        end.
        ''';

procedure TMultifileTests.TestUsesVisibility_TransitiveTypeArgRejected;
const
  ProgSrc =
    '''
        program P;
        uses VisBase, VisGen;
        var
          B: TGenBox<TUnitRec>;
        begin
          B := TGenBox<TUnitRec>.Create()
        end.
        ''';
var
  Msg: string;
begin
  Msg := AnalyseUnitsAndProg([VisTypesSrc, VisBaseSrc, VisHelpSrc, VisGenSrc], ProgSrc);
  AssertTrue('type argument of an unused unit rejected: ' + Msg,
    Pos('TUnitRec', Msg) >= 0);
  AssertTrue('names the unit to add: ' + Msg,
    Pos('declared in unit ''VisTypes''', Msg) >= 0);
end;

procedure TMultifileTests.TestUsesVisibility_GenericBodySeesDeclaringUnitUses;
const
  ProgSrc =
    '''
        program P;
        uses VisGen;
        var
          B: TGenBox<Integer>;
          N: Integer;
        begin
          B := TGenBox<Integer>.Create();
          N := B.Bumped()
        end.
        ''';
begin
  AssertEquals('generic class body resolves in its declaring unit', '',
    AnalyseUnitsAndProg([VisHelpSrc, VisGenSrc], ProgSrc));
end;

procedure TMultifileTests.TestUsesVisibility_GenericFuncBodySeesDeclaringUnitUses;
const
  ProgSrc =
    '''
        program P;
        uses VisGen;
        var
          N: Integer;
        begin
          N := GenBump<Integer>(3)
        end.
        ''';
begin
  AssertEquals('generic function body resolves in its declaring unit', '',
    AnalyseUnitsAndProg([VisHelpSrc, VisGenSrc], ProgSrc));
end;

procedure TMultifileTests.TestUsesVisibility_GenericOverConsumerType;
const
  ProgSrc =
    '''
        program P;
        uses VisGen;
        type
          TProgRec = record
            A: Integer;
          end;
        procedure Run();
        type
          TLocalRec = record
            B: Integer;
          end;
        var
          B1: TGenBox<TProgRec>;
          B2: TGenBox<TLocalRec>;
          N: Integer;
        begin
          B1 := TGenBox<TProgRec>.Create();
          B2 := TGenBox<TLocalRec>.Create();
          N := B1.Bumped() + B2.Bumped() + GenBump<TProgRec>(B1.FValue)
        end;
        begin
          Run()
        end.
        ''';
begin
  AssertEquals('type arguments declared by the consumer still resolve', '',
    AnalyseUnitsAndProg([VisHelpSrc, VisGenSrc], ProgSrc));
end;

procedure TMultifileTests.TestUsesVisibility_UnitShadowsSystemPointerAlias;
const
  OwnSrc =
    '''
        unit VisOwnPtr;
        interface
        type
          PInteger = ^Byte;
        function Peek(P: PInteger): Integer;
        implementation
        function Peek(P: PInteger): Integer;
        begin
          Result := P^
        end;
        end.
        ''';
  MidSrc =
    '''
        unit VisPtrMid;
        interface
        function MidPeek(): Integer;
        implementation
        uses VisOwnPtr;
        function MidPeek(): Integer;
        var
          B: Byte;
        begin
          B := 3;
          Result := Peek(@B)
        end;
        end.
        ''';
  NotUsingSrc =
    '''
        program P;
        uses VisPtrMid;
        var
          I: Integer;
          Q: PInteger;
        begin
          Q := @I;
          Q^ := MidPeek()
        end.
        ''';
  UsingSrc =
    '''
        program P;
        uses VisOwnPtr;
        var
          B: Byte;
          Q: PInteger;
        begin
          Q := @B;
          B := Peek(Q)
        end.
        ''';
begin
  AssertEquals('System''s PInteger despite a hidden unit''s own', '',
    AnalyseUnitsAndProg([OwnSrc, MidSrc], NotUsingSrc));
  AssertEquals('the used unit''s PInteger wins over System''s', '',
    AnalyseUnitsAndProg([OwnSrc], UsingSrc));
end;

initialization
  RegisterTest(TMultifileTests);
end.
