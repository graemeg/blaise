{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.staticmembers;

{ E2E tests for `static` class/record members: static var, static method,
  static property, and the lazy-singleton pattern.  Each program is compiled
  and run on every backend (QBE + native).  Parser/semantic/IR tests live in
  cp.test.staticmembers.pas; these guard the codegen -> QBE -> run boundary
  the IR harness cannot see (data-slot emission, no-Self call ABI, qualified
  static reads). }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStaticMembersTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { TFoo.StaticArr[I] reads / writes one element of a static or dynamic
      array, and a default property through a static object }
    procedure TestRun_StaticVar_ElementReadWrite;
    { BARE element and field writes to static vars inside methods of their
      class -- array, dynamic array and record static vars, from a static
      and an instance method, in a program and in a unit.  They stored to a
      symbol under the declared name: an undefined-symbol link error on
      macOS, a libc lookup and exit 255 on Linux. }
    procedure TestRun_StaticVar_BareWritesInsideMethods;
    { a static method called through an instance, in expression and
      statement position: x86-64 passed the instance as a first argument,
      so the method read it as its first parameter }
    procedure TestRun_StaticMethodThroughInstance_NoSelf;
    { a float static property read: compiling it crashed the x86-64
      compiler }
    procedure TestRun_StaticFloatProperty_Read;
    { a static getter's object result is released by every consumer: as a
      field base (TFoo.SP.N), an argument, and stored (X := TFoo.SP) }
    procedure TestRun_StaticGetterResult_Released;
    { static properties through every receiver form -- the type name, an
      instance, bare in an instance method and in a static method -- of
      string, object, Double, record and indexed kind, method- or
      static-var-backed; objects stored through them are freed }
    procedure TestRun_StaticProperties_EveryForm;
    { a static var declared in ANOTHER unit, written and read through the
      type name: arm64 refused the store/load (its label was not known as a
      global of this translation unit) }
    procedure TestRun_StaticVar_CrossUnit;
    { Static members of aggregate type: a record static var's field
      (TC.SB.S), a record / closure static property, a static method returning
      a closure called directly, and `inherited GetT();` for an interface
      result.  x86-64 read the static record as a pointer and crashed. }
    procedure TestRun_StaticAggregateMembers;
    procedure TestRun_StaticVar_ReleasedAtExit_AndIntfFirstArg;
    procedure TestRun_StaticMethod_NoSelf;
    procedure TestRun_StaticVar_SharedAcrossCalls;
    procedure TestRun_StaticVar_QualifiedRead;
    procedure TestRun_StaticVar_QualifiedWrite_Scalar;
    procedure TestRun_StaticVar_QualifiedWrite_ClassARC;
    procedure TestRun_StaticVar_InterfaceStore;
    procedure TestRun_StaticVar_ChainedLValueBase;
    procedure TestRun_StaticVar_LValueUses;
    { BUG-20260720-static-var-string-unsupported: a string static var round-trips
      (store retains, exit release), and a dyn-array static var stores + Length +
      releases at exit — both leak-free on both backends. }
    procedure TestRun_StaticVar_StringAndDynArray;
    procedure TestRun_StaticProperty_QualifiedRead;
    procedure TestRun_Singleton_LazyGetInstance;
    procedure TestRun_StaticConst_OnClass;
    procedure TestRun_RecordStaticFactory;
    { BUG-036: a method declared AFTER a bare `static var` block must stay an
      instance method and see instance fields. }
    procedure TestRun_MethodAfterStaticVar_SeesInstanceFields;
    { RECORD static methods called through the TYPE NAME in STATEMENT
      position (TVal.Note(1); / discarded TVal.Make(2);) — the resolver
      only accepted class types there ('TVal' is not a variable). }
    procedure TestRun_RecordStaticCall_StatementPosition;
    { TC.A[I] / TC.S[K], static indexed properties read from the program and
      from an instance method: the index reaches the static getter (it was
      dropped -- a wrong value on arm64, a crash on x86-64) }
    procedure TestRun_StaticIndexedPropertyRead;
  end;

implementation

procedure TE2EStaticMembersTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-staticmembers')
end;

procedure TE2EStaticMembersTests.TestRun_StaticMethod_NoSelf;
const Src =
  '''
  program P;
  type
    TMath = class
    public
      static function Square(X: Integer): Integer;
    end;
  static function TMath.Square(X: Integer): Integer;
  begin
    Result := X * X;
  end;
  begin
    WriteLn(TMath.Square(7))
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '49' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_SharedAcrossCalls;
const Src =
  '''
  program P;
  type
    TCounter = class
    private static var
      FN: Integer;
    public
      static function Next: Integer;
    end;
  static function TCounter.Next: Integer;
  begin
    FN := FN + 1;
    Result := FN;
  end;
  begin
    WriteLn(TCounter.Next());
    WriteLn(TCounter.Next());
    WriteLn(TCounter.Next())
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '2' + LE + '3' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedRead;
const Src =
  '''
  program P;
  type
    TCounter = class
    public static var
      Total: Integer;
      static procedure Bump;
    end;
  static procedure TCounter.Bump;
  begin
    Total := Total + 10;
  end;
  begin
    TCounter.Bump();
    TCounter.Bump();
    WriteLn(TCounter.Total)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '20' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedWrite_Scalar;
const Src =
  '''
  program P;
  type
    TFoo = class
    public static var
      GCount: Integer;
    end;
  begin
    TFoo.GCount := 5;
    TFoo.GCount := TFoo.GCount + 37;
    WriteLn(TFoo.GCount)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedWrite_ClassARC;
const Src =
  '''
  program P;
  type
    TObj = class
    public
      V: Integer;
    end;
    THolder = class
    public static var
      GObj: TObj;
    end;
  var local: TObj;
  begin
    THolder.GObj := TObj.Create();
    local := THolder.GObj;
    local.V := 99;
    WriteLn(local.V);
    THolder.GObj := nil;
    if THolder.GObj = nil then WriteLn('released')
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '99' + LineEnding + 'released' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_InterfaceStore;
{ Interface-typed static var: the bare store inside a static method
  (FCache := X) must write BOTH slots of the 2-slot fat pointer (obj + itab)
  with correct ARC, and the bare read (Result := FCache) must reconstruct it.
  Regression for the static-call interface-arg leading-comma bug that made
  THolder.SetIt(T) emit an invalid QBE call and segfault native. }
const Src =
  '''
  program P;
  type
    IThing = interface
      procedure Speak;
    end;
    TThing = class(IThing)
    public
      Tag: Integer;
      procedure Speak;
    end;
    THolder = class
    public static var
      FCache: IThing;
      static procedure SetIt(X: IThing);
      static function GetIt: IThing;
    end;
  procedure TThing.Speak;
  begin
    WriteLn('thing ', Tag);
  end;
  static procedure THolder.SetIt(X: IThing);
  begin
    FCache := X;
  end;
  static function THolder.GetIt: IThing;
  begin
    Result := FCache;
  end;
  var
    T: TThing;
    Got: IThing;
  begin
    T := TThing.Create();
    T.Tag := 7;
    THolder.SetIt(T);
    Got := THolder.GetIt();
    Got.Speak();
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'thing 7' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_ChainedLValueBase;
{ A qualified static var of class type used as the BASE of a further l-value
  chain: 'TFoo.GObj.Field := V' (field write through the chained base) and
  'TFoo.GObj.Method()' (method call on the chained base).  The read form
  (TFoo.GObj.Field as an expression) already worked; the write/call receiver
  path through the chained base was unresolved ("Field access requires a record
  or class base, got 'class of TFoo'"). }
const Src =
  '''
  program P;
  type
    TObj = class
    public
      V: Integer;
      procedure Bump;
    end;
    THolder = class
    public static var
      GObj: TObj;
    end;
  procedure TObj.Bump;
  begin
    V := V + 1;
  end;
  begin
    THolder.GObj := TObj.Create();
    WriteLn(THolder.GObj.V);
    THolder.GObj.V := 5;
    WriteLn(THolder.GObj.V);
    THolder.GObj.Bump();
    WriteLn(THolder.GObj.V);
    THolder.GObj := nil
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '0' + LE + '5' + LE + '6' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_LValueUses;
{ A qualified static var used as an L-VALUE — passed by reference (Inc, a var
  parameter), its address taken (@), or as the receiver of the built-in Free.
  Its storage IS the mangled global slot, so every l-value-address path must
  address that slot directly rather than treat the bare class-name base as a
  variable / field of an instance.  All four forms previously miscompiled or
  crashed (link-relocation against the class name, a nil-FieldInfo abort, or
  garbage/segfault at runtime). }
const Src =
  '''
  program P;
  type
    TObj = class
    public
      V: Integer;
    end;
    THolder = class
    public static var
      Counter: Integer;
      GObj: TObj;
    end;
  procedure Bump(var X: Integer);
  begin X := X + 10 end;
  var Ptr: ^Integer;
  begin
    THolder.Counter := 0;
    Inc(THolder.Counter);          { Inc: static var by reference }
    Bump(THolder.Counter);         { var parameter: static var by reference }
    Ptr := @THolder.Counter;       { address-of a static var }
    WriteLn(Ptr^);                 { 11 }
    THolder.GObj := TObj.Create();
    THolder.GObj.Free();           { built-in Free through the static var }
    if THolder.GObj = nil then WriteLn('freed')
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '11' + LE + 'freed' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticProperty_QualifiedRead;
const Src =
  '''
  program P;
  type
    TRegistry = class
    private static var
      FCounter: Integer;
    public
      static function NextId: Integer;
      static property Counter: Integer read NextId;
    end;
  static function TRegistry.NextId: Integer;
  begin
    FCounter := FCounter + 1;
    Result := FCounter;
  end;
  begin
    WriteLn(TRegistry.Counter);
    WriteLn(TRegistry.Counter)
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '2' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_Singleton_LazyGetInstance;
const Src =
  '''
  program P;
  type
    TConfig = class
    private static var
      FInstance: TConfig;
    public
      FValue: Integer;
      static function Instance: TConfig;
    end;
  static function TConfig.Instance: TConfig;
  begin
    if FInstance = nil then
      FInstance := TConfig.Create();
    Result := FInstance;
  end;
  begin
    TConfig.Instance().FValue := 42;
    WriteLn(TConfig.Instance().FValue)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticConst_OnClass;
const Src =
  '''
  program P;
  type
    TLimits = class
    public static const
      MaxItems = 128;
    end;
  begin
    WriteLn(TLimits.MaxItems)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '128' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_RecordStaticFactory;
const Src =
  '''
  program P;
  type
    TPoint = record
      X, Y: Integer;
      static function Make(AX, AY: Integer): TPoint;
    end;
  static function TPoint.Make(AX, AY: Integer): TPoint;
  begin
    Result.X := AX;
    Result.Y := AY;
  end;
  var Pt: TPoint;
  begin
    Pt := TPoint.Make(3, 4);
    WriteLn(Pt.X + Pt.Y)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '7' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_MethodAfterStaticVar_SeesInstanceFields;
const
  Src = '''
    program p;
    type
      TLogger = class
      private
        FName: string;
      public
        constructor Create(AName: string); overload;
        static var Level: Integer;
        procedure Log;
      end;
    constructor TLogger.Create(AName: string);
    begin
      FName := AName
    end;
    procedure TLogger.Log;
    begin
      WriteLn(FName, ':', TLogger.Level)
    end;
    var L: TLogger;
    begin
      TLogger.Level := 3;
      L := TLogger.Create('hello');
      L.Log()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hello:3' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_RecordStaticCall_StatementPosition;
const
  Src = '''
    program prg;
    type
      TVal = record
        X: Integer;
        static function Make(A: Integer): TVal;
        static procedure Note(A: Integer);
      end;
    static function TVal.Make(A: Integer): TVal;
    begin
      WriteLn('make ', A);
      Result.X := A
    end;
    static procedure TVal.Note(A: Integer);
    begin
      WriteLn('note ', A)
    end;
    begin
      TVal.Note(1);      { record static procedure, statement position }
      TVal.Make(2)       { record static FUNCTION, result discarded }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'note 1' + LineEnding + 'make 2' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_StringAndDynArray;
begin
  { String static var: write (retain new / release old), read, and program-exit
    release — all leak-free. }
  AssertLeakFreeOnAll(
    '''
    program P;
    type THolder = class static var SS: string; end;
    begin
      THolder.SS := 'hi';
      WriteLn(THolder.SS);
      THolder.SS := 'bye';
      WriteLn(THolder.SS)
    end.
    ''', 'bye');
  { Dyn-array static var: store from a dyn-array value + Length + exit release. }
  AssertLeakFreeOnAll(
    '''
    program P;
    type THolder = class static var DA: array of Integer; end;
    var Local: array of Integer; L: Integer;
    begin
      SetLength(Local, 3);
      THolder.DA := Local;
      L := Length(THolder.DA);
      WriteLn(L)
    end.
    ''', '3');
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_ReleasedAtExit_AndIntfFirstArg;
const
  {
    A class-typed static var is a program-lifetime global and is released at
    program exit (its destructor runs after the main block); a static method
    whose FIRST parameter is an interface receives the (obj, itab) pair with no
    Self ahead of it. }
  Src = '''
    program StaticExit;
    type
      IThing = interface
        procedure Speak;
      end;
      TThing = class(IThing)
      public
        procedure Speak;
      end;
      THolder = class
      public
        static procedure SetIt(X: IThing);
      end;
      TFoo = class
      static var
        FInst: TFoo;
      public
        destructor Destroy; override;
      end;
    procedure TThing.Speak;
    begin WriteLn('thing speaks') end;
    static procedure THolder.SetIt(X: IThing);
    begin X.Speak() end;
    destructor TFoo.Destroy;
    begin WriteLn('TFoo freed at exit'); inherited Destroy() end;
    var T: TThing;
    begin
      T := TThing.Create();
      THolder.SetIt(T);
      TFoo.FInst := TFoo.Create();
      WriteLn('main done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'thing speaks' + #10 +
    'main done' + #10 +
    'TFoo freed at exit' + #10, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticIndexedPropertyRead;
const
  Src = '''
    program StIdx;
    type
      TC = class
      private static var
        FA: array[0..3] of Integer;
      public
        static function GetA(I: Integer): Integer;
        static function GetS(const K: String): String;
        static property A[I: Integer]: Integer read GetA;
        static property S[K: String]: String read GetS;
        procedure Run;
      end;
    static function TC.GetA(I: Integer): Integer; begin Result := FA[I] + I end;
    static function TC.GetS(const K: String): String; begin Result := K + '!' end;
    procedure TC.Run; begin WriteLn(TC.A[1], ' ', TC.S['in']) end;
    var X: Integer; Str: String; O: TC;
    begin
      X := TC.A[2];
      Str := TC.S['k'];
      WriteLn(X, ' ', TC.A[3], ' ', Str, ' ', TC.S['z']);
      O := TC.Create();
      O.Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2 3 k! z!' + #10 + '1 in!' + #10, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticAggregateMembers;
const
  Src = '''
    program k;
    type
      TBig = record A, B, C: Int64; S: string; end;
      TKFn = reference to function(A: Integer): Integer;
      IThing = interface
        function Name(): string;
      end;
      TC = class(TObject, IThing)
      public static var
        SB: TBig;
      public
        FN: string;
        function Name(): string;
        function GetT(): IThing; virtual;
        procedure Touch(); virtual;
        static function GetSB(): TBig;
        static function GetSF(): TKFn;
        static property PSB: TBig read GetSB;
        static property PSF: TKFn read GetSF;
      end;
      TD = class(TC)
        function GetT(): IThing; override;
        procedure Touch(); override;
      end;
    function TC.Name(): string; begin Result := FN; end;
    function TC.GetT(): IThing; var C: TC; begin C := TC.Create(); C.FN := 'base'; Result := C; end;
    procedure TC.Touch(); begin end;
    static function TC.GetSB(): TBig; begin Result.S := 'sb' + IntToStr(1); Result.B := 9; end;
    static function TC.GetSF(): TKFn; begin Result := function(A: Integer): Integer begin Result := A * 7; end; end;
    function TD.GetT(): IThing; begin inherited GetT(); end;
    procedure TD.Touch(); begin inherited GetT(); end;
    procedure Show(const B: TBig); begin WriteLn('show ', B.S, ' ', B.B); end;
    var D: TD; I: IThing; B: TBig; F: TKFn;
    begin
      D := TD.Create();
      I := D.GetT();
      WriteLn('1 ', I.Name());
      WriteLn('2 ', D.GetT().Name());
      D.Touch();
      WriteLn('3 ', TC.PSB.S, ' ', TC.PSB.B);
      B := TC.PSB;
      WriteLn('4 ', B.S);
      Show(TC.PSB);
      F := TC.PSF;
      WriteLn('5 ', F(2), ' ', TC.GetSF()(3));
      TC.SB.S := 'svar';
      WriteLn('6 ', TC.SB.S);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 base' + LineEnding +
    '2 base' + LineEnding +
    '3 sb1 9' + LineEnding +
    '4 sb1' + LineEnding +
    'show sb1 9' + LineEnding +
    '5 14 21' + LineEnding +
    '6 svar' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_ElementReadWrite;
const
  Src = '''
    program P;
    type
      TIA = array of Integer;
      TItems = class
        FData: array[0..3] of Integer;
        function GetItem(I: Integer): Integer;
        procedure SetItem(I: Integer; V: Integer);
        property Items[I: Integer]: Integer read GetItem write SetItem; default;
      end;
      TC = class
        static var V: TIA;
        static var S: array[0..2] of Integer;
        static var Names: array of string;
        static var Box: TItems;
        static procedure Show;
      end;
    function TItems.GetItem(I: Integer): Integer;
    begin
      Result := FData[I];
    end;
    procedure TItems.SetItem(I: Integer; V: Integer);
    begin
      FData[I] := V;
    end;
    static procedure TC.Show;
    begin
      WriteLn(V[0], ' ', S[2], ' ', Names[1]);
    end;
    var
      X: Integer;
      N: string;
    begin
      SetLength(TC.V, 2);
      TC.V[1] := 5;
      TC.V[0] := TC.V[1] + 1;
      X := TC.V[1];
      WriteLn(X, ' ', TC.V[0]);
      TC.S[2] := 7;
      TC.S[0] := TC.S[2] * 2;
      WriteLn(TC.S[0], ' ', TC.S[2]);
      TC.Names := ['a', 'b'];
      N := 'n' + IntToStr(X);
      TC.Names[1] := N;
      WriteLn(TC.Names[0], TC.Names[1], Length(TC.Names[1]));
      TC.Box := TItems.Create();
      TC.Box[2] := 9;
      WriteLn(TC.Box[2]);
      TC.Show();
    end.
    ''';
var
  LE: string;
  RunOut: string;
  Code: Int;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '5 6' + LE + '14 7' + LE + 'an52' + LE + '9' + LE + '6 7 n5' + LE, 0);
  AssertTrue('native compile+run (--debug)',
    CompileAndRunWithRTLDebugOn(beNative, Src, RunOut, Code, True));
  AssertEquals('native exit 0 (output: ' + RunOut + ')', 0, Code);
  AssertTrue('native no leak report, got: ' + RunOut, Pos('leak', RunOut) < 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_BareWritesInsideMethods;
const
  Decls = '''
    type
      TPt = record X, Y: Integer; end;
      THost = class
      private static var
        FSArr: array[0..3] of Integer;
        FDyn: array of string;
        FPt: TPt;
        FN: Integer;
      public
        static procedure Put(I, V: Integer);
        static function Take(I: Integer): Integer;
        procedure Fill;
        function Sum: Integer;
      end;
    ''';
  Impl = '''
    static procedure THost.Put(I, V: Integer);
    begin
      FSArr[I] := V;
      FN := FN + 1;
    end;
    static function THost.Take(I: Integer): Integer;
    begin
      Result := FSArr[I];
    end;
    procedure THost.Fill;
    begin
      SetLength(FDyn, 2);
      FDyn[0] := 'a';
      FDyn[1] := 'b' + FDyn[0];
      FPt.X := 3;
      FPt.Y := FPt.X + 1;
      FSArr[3] := 40;
    end;
    function THost.Sum: Integer;
    begin
      Result := FSArr[0] + FSArr[3] + FPt.X + FPt.Y + Length(FDyn[1]) + FN;
    end;
    ''';
  Main = '''
    var
      H: THost;
    begin
      THost.Put(0, 9);
      WriteLn(THost.Take(0));
      H := THost.Create();
      H.Fill();
      WriteLn(H.Sum());
    end.
    ''';
var
  LE: string;
  RunOut: string;
  Code: Int;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('program P;' + LE + Decls + Impl + Main, '9' + LE + '59' + LE, 0);
  AssertTrue('unit form compile+run: ' + RunOut,
    CompileAndRunWithUnit('SHost',
      'unit SHost;' + LE + 'interface' + LE + Decls + 'implementation' + LE +
      Impl + 'end.' + LE,
      'program P;' + LE + 'uses SHost;' + LE + Main, RunOut, Code));
  AssertEquals('unit form exit code', 0, Code);
  AssertEquals('unit form stdout', '9' + LE + '59' + LE, RunOut);
end;

procedure TE2EStaticMembersTests.TestRun_StaticMethodThroughInstance_NoSelf;
const
  Src = '''
    program P;
    type
      THost = class
      public
        procedure Dummy;
      private static var
        FSS: string;
      public
        static function GetIx(I: Integer): Integer;
        static procedure SetSS(const AV: string);
        static function GetSS: string;
      end;
    procedure THost.Dummy; begin end;
    static function THost.GetIx(I: Integer): Integer; begin Result := I * 10; end;
    static procedure THost.SetSS(const AV: string); begin FSS := AV; end;
    static function THost.GetSS: string; begin Result := FSS; end;
    var
      H: THost;
    begin
      H := THost.Create();
      WriteLn(H.GetIx(4));
      H.SetSS('q');
      WriteLn(H.GetSS(), ' ', THost.GetIx(2));
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '40' + LE + 'q 20' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticFloatProperty_Read;
const
  Src = '''
    program P;
    type
      THost = class
      public
        procedure Dummy;
        static function GetSD: Double;
        static property SD: Double read GetSD;
      end;
    procedure THost.Dummy; begin end;
    static function THost.GetSD: Double; begin Result := 2.5; end;
    var
      D: Double;
    begin
      WriteLn(THost.SD:0:1);
      D := THost.SD + 1.0;
      WriteLn(D:0:1);
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2.5' + LE + '3.5' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticGetterResult_Released;
const
  Src = '''
    program P;
    type
      TItem = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
      THost = class
      public
        procedure Dummy;
      private static var
        FSO: TItem;
      public
        static procedure SetSO(AV: TItem);
        static function GetSO: TItem;
        static property SO: TItem read GetSO;
      end;
    constructor TItem.Create(AN: Integer); begin N := AN; end;
    destructor TItem.Destroy; begin WriteLn('free ', N); end;
    procedure THost.Dummy; begin end;
    static procedure THost.SetSO(AV: TItem); begin FSO := AV; end;
    static function THost.GetSO: TItem; begin Result := FSO; end;
    procedure Show(AV: TItem); begin WriteLn('show ', AV.N); end;
    procedure Run;
    var
      X: TItem;
    begin
      THost.SetSO(TItem.Create(1));
      X := THost.SO;
      X := nil;
      Show(THost.SO);
      WriteLn(THost.SO.N);
      THost.SetSO(nil);
      WriteLn('after reset');
    end;
    begin
      Run();
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'show 1' + LE + '1' + LE + 'free 1' + LE + 'after reset' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticProperties_EveryForm;
const
  Src = '''
    program P;
    uses SysUtils;
    type
      TItem = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
      TPair = record A, B: Int64; end;
      THost = class
      private static var
        FSS: string;
        FSO: TItem;
        FSD: Double;
        FSP: TPair;
        FArr: array[0..3] of Integer;
        FFI: Integer;
      public
        procedure Inside;
        static function GetSS: string;
        static procedure SetSS(const AV: string);
        static function GetSO: TItem;
        static procedure SetSO(AV: TItem);
        static function GetSD: Double;
        static procedure SetSD(AV: Double);
        static function GetSP: TPair;
        static procedure SetSP(const AV: TPair);
        static function GetIx(I: Integer): Integer;
        static procedure SetIx(I: Integer; AV: Integer);
        static property SS: string read GetSS write SetSS;
        static property SO: TItem read GetSO write SetSO;
        static property SD: Double read GetSD write SetSD;
        static property SP: TPair read GetSP write SetSP;
        static property Ix[I: Integer]: Integer read GetIx write SetIx;
        static property FI: Integer read FFI write FFI;
        static procedure SInside;
      end;
    constructor TItem.Create(AN: Integer); begin N := AN; end;
    destructor TItem.Destroy; begin WriteLn('free ', N); end;
    static function THost.GetSS: string; begin Result := FSS; end;
    static procedure THost.SetSS(const AV: string); begin FSS := AV; end;
    static function THost.GetSO: TItem; begin Result := FSO; end;
    static procedure THost.SetSO(AV: TItem); begin FSO := AV; end;
    static function THost.GetSD: Double; begin Result := FSD; end;
    static procedure THost.SetSD(AV: Double); begin FSD := AV; end;
    static function THost.GetSP: TPair; begin Result := FSP; end;
    static procedure THost.SetSP(const AV: TPair); begin FSP := AV; end;
    static function THost.GetIx(I: Integer): Integer; begin Result := FArr[I]; end;
    static procedure THost.SetIx(I: Integer; AV: Integer); begin FArr[I] := AV; end;
    procedure THost.Inside;
    begin
      SS := 'in' + IntToStr(1);
      SO := TItem.Create(10);
      SD := 1.5;
      Ix[1] := 11;
      FI := 12;
      WriteLn('inside ', SS, ' ', SO.N, ' ', SD:0:1, ' ', Ix[1], ' ', FI);
      SO := nil;
    end;
    static procedure THost.SInside;
    begin
      SS := 'sin';
      SO := TItem.Create(20);
      Ix[2] := 21;
      FI := 22;
      WriteLn('sinside ', SS, ' ', SO.N, ' ', Ix[2], ' ', FI);
      SO := nil;
    end;
    function MkS(N: Integer): string; begin Result := 'v' + IntToStr(N); end;
    function MkP: TPair; begin Result.A := 7; Result.B := 8; end;
    var
      H: THost;
    begin
      H := THost.Create();
      THost.SS := MkS(1);
      THost.SO := TItem.Create(1);
      THost.SD := 2.5;
      THost.SP := MkP();
      THost.Ix[0] := 5;
      THost.FI := 6;
      WriteLn('cls ', THost.SS, ' ', THost.SO.N, ' ', THost.SD:0:1, ' ',
        THost.SP.B, ' ', THost.Ix[0], ' ', THost.FI);
      H.SS := MkS(2);
      H.SO := TItem.Create(2);
      H.SD := 3.5;
      H.Ix[3] := 9;
      H.FI := 7;
      WriteLn('inst ', H.SS, ' ', H.SO.N, ' ', H.SD:0:1, ' ', H.SP.A, ' ',
        H.Ix[3], ' ', H.FI);
      H.SO := nil;
      H.Inside();
      THost.SInside();
      WriteLn('end');
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'cls v1 1 2.5 8 5 6' + LE + 'free 1' + LE +
    'inst v2 2 3.5 7 9 7' + LE + 'free 2' + LE +
    'inside in1 10 1.5 11 12' + LE + 'free 10' + LE +
    'sinside sin 20 21 22' + LE + 'free 20' + LE + 'end' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_CrossUnit;
const
  USrc = '''
    unit CProps;
    interface
    type
      TC = class
      public
        procedure Dummy;
      public static var
        SV: Integer;
        SName: string;
      end;
    implementation
    procedure TC.Dummy; begin end;
    end.
    ''';
  Src = '''
    program P;
    uses CProps;
    begin
      TC.SV := 4;
      TC.SName := 'n' + 'x';
      TC.SV := TC.SV + 1;
      WriteLn(TC.SV, ' ', TC.SName);
    end.
    ''';
var
  LE: string;
  RunOut: string;
  Code: Int;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + RunOut,
    CompileAndRunWithUnit('CProps', USrc, Src, RunOut, Code));
  AssertEquals('exit code', 0, Code);
  AssertEquals('stdout', '5 nx' + LE, RunOut);
end;

initialization
  RegisterTest(TE2EStaticMembersTests);

end.
