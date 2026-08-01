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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe,
  uUnitLoader;

type
  TMultifileTests = class(TTestCase)
  private
    FTmpDir: string;
    procedure WriteUnit(const AName, ASrc: string);
    function  MakeSearchPaths: TStringList;
    function  ParseProg(const ASrc: string): TProgram;
    function  ParseUnitSrc(const ASrc: string): TUnit;
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
    { Combined code generation                                             }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TwoFileCompile_UnitFuncExported;
    procedure TestCodegen_TwoFileCompile_MainPresent;
    { Two used units export the same global var name; a qualified reference
      'Unit.V' must emit each unit's own owner-prefixed storage symbol so the
      two refer to distinct slots rather than colliding on a bare '$V'. }
    procedure TestCodegen_CrossUnitQualifiedVar_DistinctSymbols;
    { Two used units export a class of the same name; each unit's codegen pass
      must emit its type's storage symbols (typeinfo/vtable/__cn) keyed on its
      own unit, so the two coexist instead of colliding on the flat winner. }
    procedure TestCodegen_CrossUnitType_DistinctSymbols;
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
{ Combined code generation tests                                       }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestCodegen_TwoFileCompile_UnitFuncExported;
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
  CG:   TCodeGenQBE;
  IR:   string;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  CG   := TCodeGenQBE.Create();
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    CG.AppendUnit(U);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput();
    AssertTrue('unit func exported',
      (Pos('export function', IR) > 0) and (Pos('$MathU_Add', IR) > 0));
  finally
    CG.Free();
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TMultifileTests.TestCodegen_TwoFileCompile_MainPresent;
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
  CG:   TCodeGenQBE;
  IR:   string;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  CG   := TCodeGenQBE.Create();
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    CG.AppendUnit(U);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput();
    AssertTrue('main function present',
      (Pos('export function', IR) > 0) and (Pos('$main', IR) > 0));
  finally
    CG.Free();
    SA.Free();
    Prog.Free();
    U.Free();
  end;
end;

procedure TMultifileTests.TestCodegen_CrossUnitQualifiedVar_DistinctSymbols;
const
  UnitA =
    '''
        unit uva;
        interface
        var V: Integer = 7;
        implementation
        end.
        ''';
  UnitB =
    '''
        unit uvb;
        interface
        var V: Integer = 9;
        implementation
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses uva, uvb;
        var r: Integer;
        begin
          r := uva.V;
          r := uvb.V
        end.
        ''';
var
  UA, UB: TUnit;
  Prog:   TProgram;
  SA:     TSemanticAnalyser;
  CG:     TCodeGenQBE;
  IR:     string;
begin
  UA   := ParseUnitSrc(UnitA);
  UB   := ParseUnitSrc(UnitB);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  CG   := TCodeGenQBE.Create();
  try
    SA.AnalyseUnitForExport(UA);
    SA.AnalyseUnitForExport(UB);
    SA.Analyse(Prog);
    CG.AppendUnit(UA);
    CG.AppendUnit(UB);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput();
    { Each unit defines its own owner-prefixed slot, and the qualified loads
      reference both — proving the two same-named vars do not collapse. }
    AssertTrue('uva.V slot referenced', Pos('$uva_V', IR) > 0);
    AssertTrue('uvb.V slot referenced', Pos('$uvb_V', IR) > 0);
  finally
    CG.Free();
    SA.Free();
    Prog.Free();
    UB.Free();
    UA.Free();
  end;
end;

procedure TMultifileTests.TestCodegen_CrossUnitType_DistinctSymbols;
const
  UnitA =
    '''
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
  UnitB =
    '''
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
  ProgSrc =
    '''
        program TestP;
        uses tca, tcb;
        var S: TShape;
        begin
          S := TShape.Create()
        end.
        ''';
var
  UA, UB: TUnit;
  Prog:   TProgram;
  SA:     TSemanticAnalyser;
  CG:     TCodeGenQBE;
  IR:     string;
begin
  UA   := ParseUnitSrc(UnitA);
  UB   := ParseUnitSrc(UnitB);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create();
  CG   := TCodeGenQBE.Create();
  try
    SA.AnalyseUnitForExport(UA);
    SA.AnalyseUnitForExport(UB);
    SA.Analyse(Prog);
    CG.SetSymbolTable(Prog.SymbolTable);
    CG.AppendUnit(UA);
    CG.AppendUnit(UB);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput();
    { Each unit emits its own owner-prefixed type symbols — no collision on a
      single bare/winner symbol, and both class-name string blobs are distinct. }
    AssertTrue('tca typeinfo', Pos('typeinfo_tca_TShape', IR) > 0);
    AssertTrue('tcb typeinfo', Pos('typeinfo_tcb_TShape', IR) > 0);
    AssertTrue('tca vtable',   Pos('vtable_tca_TShape', IR) > 0);
    AssertTrue('tcb vtable',   Pos('vtable_tcb_TShape', IR) > 0);
    AssertTrue('tca classname', Pos('__cn_tca_TShape', IR) > 0);
    AssertTrue('tcb classname', Pos('__cn_tcb_TShape', IR) > 0);
  finally
    CG.Free();
    SA.Free();
    Prog.Free();
    UB.Free();
    UA.Free();
  end;
end;

initialization
  RegisterTest(TMultifileTests);
end.
