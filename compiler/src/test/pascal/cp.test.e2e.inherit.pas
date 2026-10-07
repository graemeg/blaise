{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.inherit;

{ End-to-end tests for class inheritance — compile + run on BOTH backends.
  Grew out of the test-hardening sweep: cp.test.inherit.pas asserted only on
  generated QBE IR substrings and never fed the IR to QBE/native, so virtual
  dispatch, inherited calls, multi-level field layout, and destructor chaining
  were never proven to actually run.  Each test here runs the program on the
  QBE backend AND the native x86-64 backend and asserts on stdout. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EInheritTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_VTable_OverrideInheritStaticAbstract;
    procedure TestRun_Inheritance_FieldsInheritedInheritsFromNil;
    procedure TestRun_Overloads_PickTheRightBody;
    procedure TestRun_TypeTests_IsAsClassType;
    procedure TestRun_ThreeLevelVirtualOverride;
    procedure TestRun_InheritedInOverride;
    procedure TestRun_CtorChainInherited;
    procedure TestRun_PolymorphicArrayDispatch;
    procedure TestRun_IsAsOperators;
    procedure TestRun_VirtualDispatchInCtor;
    procedure TestRun_FourLevelFieldInherit;
    procedure TestRun_DoubleDispatchInherited;
    procedure TestRun_VirtualDestructorChain;
    { A property whose getter/setter is virtual must dispatch through the
      vtable, exactly like a direct accessor call does. }
    procedure TestRun_VirtualPropertyGetter_Dispatches;
    procedure TestRun_VirtualPropertySetter_Dispatches;
    { A derived `overload` method must MERGE with the inherited overload set,
      not shadow it — both the base and derived variants stay callable. }
    procedure TestRun_OverloadMergeAcrossInheritance;
  end;

implementation

const
  LE = #10;

procedure TE2EInheritTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-inherit');
end;

const
  { 3-level hierarchy: a non-virtual Describe in the root calls a virtual
    Name; the most-derived override must be reached regardless of the
    static (TA) variable type. }
  SrcThreeLevel = '''
    program P;
    type
      TA = class
        function Name: string; virtual; begin Result := 'A'; end;
        function Describe: string; begin Result := 'I am ' + Self.Name(); end;
      end;
      TB = class(TA)
        function Name: string; override; begin Result := 'B'; end;
      end;
      TC = class(TB)
        function Name: string; override; begin Result := 'C'; end;
      end;
    var a: TA;
    begin
      a := TC.Create; WriteLn(a.Describe()); a := nil;
      a := TB.Create; WriteLn(a.Describe()); a := nil;
    end.
    ''';

  SrcInheritedInOverride = '''
    program P;
    type
      TBase = class
        function Greet: string; virtual; begin Result := 'base'; end;
      end;
      TDerived = class(TBase)
        function Greet: string; override; begin Result := inherited Greet() + '+derived'; end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create; WriteLn(d.Greet()); d := nil;
    end.
    ''';

  SrcCtorChain = '''
    program P;
    type
      TBase = class
        FX: Integer;
        constructor Create(ax: Integer); begin FX := ax; end;
      end;
      TDerived = class(TBase)
        FY: Integer;
        constructor Create(ax, ay: Integer); begin inherited Create(ax); FY := ay; end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create(3, 7); WriteLn(d.FX + d.FY); d := nil;
    end.
    ''';

  { Polymorphism through a base-typed array: each element dispatches to its
    own override. }
  SrcPolyArray = '''
    program P;
    type
      TShape = class
        function Area: Integer; virtual; begin Result := 0; end;
      end;
      TSquare = class(TShape)
        FS: Integer;
        constructor Create(s: Integer); begin FS := s; end;
        function Area: Integer; override; begin Result := FS * FS; end;
      end;
      TRect = class(TShape)
        FW, FH: Integer;
        constructor Create(w, h: Integer); begin FW := w; FH := h; end;
        function Area: Integer; override; begin Result := FW * FH; end;
      end;
    var shapes: array[0..1] of TShape; i, total: Integer;
    begin
      shapes[0] := TSquare.Create(4);
      shapes[1] := TRect.Create(3, 5);
      total := 0;
      for i := 0 to 1 do total := total + shapes[i].Area();
      WriteLn(total);
      shapes[0] := nil; shapes[1] := nil;
    end.
    ''';

  SrcIsAs = '''
    program P;
    type
      TAnimal = class
        function Sound: string; virtual; begin Result := '?'; end;
      end;
      TDog = class(TAnimal)
        function Sound: string; override; begin Result := 'woof'; end;
        function Fetch: string; begin Result := 'fetching'; end;
      end;
    var a: TAnimal; d: TDog;
    begin
      a := TDog.Create;
      WriteLn(a.Sound());
      if a is TDog then WriteLn('is-dog');
      d := a as TDog;
      WriteLn(d.Fetch());
      a := nil;
    end.
    ''';

  { Template-method pattern: a base constructor calls a virtual that the
    derived class overrides — the override must be reached even though the
    object is still being constructed. }
  SrcVirtualInCtor = '''
    program P;
    type
      TBase = class
        FInit: Integer;
        constructor Create; begin FInit := Self.Compute(); end;
        function Compute: Integer; virtual; begin Result := 1; end;
      end;
      TDerived = class(TBase)
        function Compute: Integer; override; begin Result := 42; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create; WriteLn(b.FInit); b := nil;
    end.
    ''';

  { Four levels, each adding a field — checks that field offsets accumulate
    correctly down the hierarchy. }
  SrcFourLevelFields = '''
    program P;
    type
      T1 = class FA: Integer; end;
      T2 = class(T1) FB: Integer; end;
      T3 = class(T2) FC: Integer; end;
      T4 = class(T3) FD: Integer; end;
    var o: T4;
    begin
      o := T4.Create;
      o.FA := 1; o.FB := 2; o.FC := 3; o.FD := 4;
      WriteLn(o.FA + o.FB * 10 + o.FC * 100 + o.FD * 1000);
      o := nil;
    end.
    ''';

  { Double dispatch: an override calls inherited Wrap, which itself calls the
    virtual Tag — Tag must resolve to the derived override. }
  SrcDoubleDispatch = '''
    program P;
    type
      TA = class
        function Tag: string; virtual; begin Result := 'a'; end;
        function Wrap: string; virtual; begin Result := '[' + Self.Tag() + ']'; end;
      end;
      TB = class(TA)
        function Tag: string; override; begin Result := 'b'; end;
        function Wrap: string; override; begin Result := 'B' + inherited Wrap(); end;
      end;
    var a: TA;
    begin
      a := TB.Create; WriteLn(a.Wrap()); a := nil;
    end.
    ''';

  SrcDestructorChain = '''
    program P;
    type
      TBase = class
        destructor Destroy; override; begin WriteLn('base-destroy'); end;
      end;
      TDerived = class(TBase)
        destructor Destroy; override; begin WriteLn('derived-destroy'); inherited Destroy(); end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create;
      d.Free();
    end.
    ''';

  { A read property backed by a VIRTUAL getter: read through a base-typed
    variable holding a derived instance must reach the override (99), just as
    a direct b.GetVal() call does. }
  SrcVirtualGetter = '''
    program P;
    type
      TBase = class
        function GetVal: Integer; virtual; begin Result := 1; end;
        property Val: Integer read GetVal;
      end;
      TDerived = class(TBase)
        function GetVal: Integer; override; begin Result := 99; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create;
      WriteLn(b.Val);
      b := nil;
    end.
    ''';

  { A write property backed by a VIRTUAL setter: assigning through a base-typed
    variable must reach the override, which records double the value. }
  SrcVirtualSetter = '''
    program P;
    type
      TBase = class
        FStore: Integer;
        procedure SetVal(AValue: Integer); virtual; begin FStore := AValue; end;
        property Val: Integer write SetVal;
      end;
      TDerived = class(TBase)
        procedure SetVal(AValue: Integer); override; begin FStore := AValue * 2; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create;
      b.Val := 21;
      WriteLn(b.FStore);
      b := nil;
    end.
    ''';

  { TDerived adds F(string) as an overload; the inherited F(Integer) must
    remain callable — the overload set merges across inheritance. }
  SrcOverloadMerge = '''
    program P;
    type
      TBase = class
        function F(x: Integer): string; overload; begin Result := 'int:' + IntToStr(x); end;
      end;
      TDerived = class(TBase)
        function F(s: string): string; overload; begin Result := 'str:' + s; end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create;
      WriteLn(d.F('a'));
      WriteLn(d.F(5));
      d := nil;
    end.
    ''';

procedure TE2EInheritTests.TestRun_ThreeLevelVirtualOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcThreeLevel, 'I am C' + LE + 'I am B' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_InheritedInOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedInOverride, 'base+derived' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_CtorChainInherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCtorChain, '10' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_PolymorphicArrayDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcPolyArray, '31' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_IsAsOperators;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIsAs, 'woof' + LE + 'is-dog' + LE + 'fetching' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualDispatchInCtor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualInCtor, '42' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_FourLevelFieldInherit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFourLevelFields, '4321' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_DoubleDispatchInherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleDispatch, 'B[b]' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualDestructorChain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDestructorChain, 'derived-destroy' + LE + 'base-destroy' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualPropertyGetter_Dispatches;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualGetter, '99' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualPropertySetter_Dispatches;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualSetter, '42' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_OverloadMergeAcrossInheritance;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOverloadMerge, 'str:a' + LE + 'int:5' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_TypeTests_IsAsClassType;
const
  {
    Run-time type tests walk the typeinfo parent chain, whose root for a class
    with no declared parent is TObject: `is` against the class, an ancestor,
    TObject and an unrelated class; `as` succeeding;
    ClassType returning the instance's own typeinfo. }
  Src = '''
    program TypeTests;
    type
      TAnimal = class
        procedure Speak; virtual; begin WriteLn('...') end;
      end;
      TDog = class(TAnimal)
        procedure Speak; override; begin WriteLn('woof') end;
      end;
      TCat = class(TAnimal) end;
    var
      A: TAnimal;
      D: TDog;
    begin
      A := TDog.Create();
      WriteLn(A is TDog, ' ', A is TAnimal, ' ', A is TObject, ' ', A is TCat);
      D := A as TDog;
      D.Speak();
      WriteLn(A.ClassType = TDog, ' ', A.ClassType = TAnimal);
      A := TCat.Create();
      WriteLn(A is TDog, ' ', A is TAnimal, ' ', A.ClassType = TCat)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'True True True False' + LE +
    'woof' + LE +
    'True False' + LE +
    'False True True' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_Overloads_PickTheRightBody;
const
  {
    Overload resolution, visible as which body runs: by arity, by parameter
    type, an exact match beating a widening one, a widening match used when it
    is the only one, class methods, virtual overloads dispatching to the
    override with the matching signature (each signature its own vtable slot),
    an overloaded method called through a field in expression context (it once
    picked the 4-parameter overload), and overloaded constructors by arity. }
  Src = '''
    program Overloads;
    type
      TFoo = class
        FA: Integer;
        procedure Show(N: Integer); overload;
        procedure Show(S: string); overload;
        constructor Create(A: Integer; B: Integer); overload;
        constructor Create(A: Integer); overload;
      end;
      TBase = class
        procedure Greet(N: Integer); overload; virtual;
        procedure Greet(S: string); overload; virtual;
      end;
      TChild = class(TBase)
        procedure Greet(N: Integer); overload; override;
        procedure Greet(S: string); overload; override;
      end;
      THelper = class
        function Run(const S: string; out R: string; out N: Integer;
                     const Args: array of string): Boolean; overload;
        function Run(const S: string; out R: string;
                     out N: Integer): Boolean; overload;
      end;
      TOwner = class
        FHelper: THelper;
        procedure DoIt;
      end;
    procedure Greet; overload;
    begin WriteLn('hello') end;
    procedure Greet(N: Integer); overload;
    begin WriteLn('greet ', N) end;
    procedure F(N: Integer); overload;
    begin WriteLn('F int ', N) end;
    procedure F(D: Double); overload;
    begin WriteLn('F double') end;
    procedure G(D: Double); overload;
    begin WriteLn('G double') end;
    procedure TFoo.Show(N: Integer);
    begin WriteLn('show int ', N) end;
    procedure TFoo.Show(S: string);
    begin WriteLn('show str ', S) end;
    constructor TFoo.Create(A: Integer; B: Integer);
    begin FA := A + B end;
    constructor TFoo.Create(A: Integer);
    begin FA := -A end;
    procedure TBase.Greet(N: Integer);
    begin WriteLn('base int ', N) end;
    procedure TBase.Greet(S: string);
    begin WriteLn('base str ', S) end;
    procedure TChild.Greet(N: Integer);
    begin WriteLn('child int ', N) end;
    procedure TChild.Greet(S: string);
    begin WriteLn('child str ', S) end;
    function THelper.Run(const S: string; out R: string; out N: Integer;
                         const Args: array of string): Boolean;
    begin R := 'with-args'; N := 1; Result := True end;
    function THelper.Run(const S: string; out R: string;
                         out N: Integer): Boolean;
    begin R := 'no-args'; N := 0; Result := True end;
    procedure TOwner.DoIt;
    var S: string; N: Integer; Ok: Boolean;
    begin
      Ok := FHelper.Run('x', S, N);
      WriteLn(S, ' ', N, ' ', Ok)
    end;
    var
      Foo: TFoo;
      B: TBase;
      O: TOwner;
    begin
      Greet();
      Greet(42);
      F(42);
      G(42);
      Foo := TFoo.Create(5);
      WriteLn(Foo.FA);
      Foo := TFoo.Create(5, 6);
      WriteLn(Foo.FA);
      Foo.Show(7);
      Foo.Show('hi');
      B := TChild.Create();
      B.Greet(1);
      B.Greet('x');
      B := TBase.Create();
      B.Greet(2);
      O := TOwner.Create();
      O.FHelper := THelper.Create();
      O.DoIt()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'hello' + LE +
    'greet 42' + LE +
    'F int 42' + LE +
    'G double' + LE +
    '-5' + LE +
    '11' + LE +
    'show int 7' + LE +
    'show str hi' + LE +
    'child int 1' + LE +
    'child str x' + LE +
    'base int 2' + LE +
    'no-args 0 True' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_Inheritance_FieldsInheritedInheritsFromNil;
const
  {
    Inheritance at run time: parent and child fields at their own offsets, an
    inherited method reached through a child instance, `inherited` with and
    without arguments, InheritsFrom on an instance (both answers) and on a
    metaclass value, and nil assignment and comparison of a self-referencing
    class field. }
  Src = '''
    program Inherit;
    type
      TAnimal = class
        Age: Integer;
      end;
      TDog = class(TAnimal)
        Legs: Integer;
      end;
      TBase = class
        X: Integer;
        procedure SetX(V: Integer);
        procedure Init; virtual;
      end;
      TChild = class(TBase)
        Y: Integer;
        procedure SetX(V: Integer);
        procedure Init; override;
      end;
      TNode = class
        Value: Integer;
        Next: TNode;
      end;
      TBaseClass = class of TBase;
    procedure TBase.SetX(V: Integer);
    begin Self.X := V end;
    procedure TBase.Init;
    begin Self.X := 100 end;
    procedure TChild.SetX(V: Integer);
    begin inherited SetX(V * 2) end;
    procedure TChild.Init;
    begin
      inherited Init();
      Self.Y := 7
    end;
    var
      D: TDog;
      C: TChild;
      B: TBase;
      N: TNode;
      MC: TBaseClass;
    begin
      D := TDog.Create();
      D.Age := 3;
      D.Legs := 4;
      WriteLn(D.Age, ' ', D.Legs);
      C := TChild.Create();
      C.Init();
      WriteLn(C.X, ' ', C.Y);
      C.SetX(21);
      WriteLn(C.X);
      B := C;
      B.SetX(5);
      WriteLn(C.X);
      MC := TChild;
      WriteLn(C.InheritsFrom(TBase), ' ', D.InheritsFrom(TBase), ' ',
        MC.InheritsFrom(TBase), ' ', MC.InheritsFrom(TDog));
      N := TNode.Create();
      N.Value := 1;
      N.Next := TNode.Create();
      WriteLn(N.Next = nil);
      N.Next := nil;
      WriteLn(N.Next = nil, ' ', N.Value)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '3 4' + LE +
    '100 7' + LE +
    '42' + LE +
    '5' + LE +
    'True False True False' + LE +
    'False' + LE +
    'True 1' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VTable_OverrideInheritStaticAbstract;
const
  {
    Virtual dispatch through the vtable: an override replaces its slot, an
    inherited virtual keeps the parent's entry, a static (non-virtual) method
    binds to the declared type, and fields sit after the vtable pointer.  An
    abstract class -- its abstract slots (and its interface's itab slot) bound
    to the runtime stub -- still builds, links and dispatches through a concrete
    subclass, both via the class and via the interface. }
  Src = '''
    program VTables;
    type
      TAnimal = class
        Name: string;
        procedure Speak; virtual;
        procedure Move; virtual;
        procedure Describe;
      end;
      TDog = class(TAnimal)
        procedure Speak; override;
        procedure Describe;
      end;
      IShape = interface
        procedure Draw;
      end;
      TShape = class(TObject, IShape)
        procedure Draw; virtual; abstract;
        procedure Area; virtual; abstract;
      end;
      TCircle = class(TShape)
        procedure Draw; override;
        procedure Area; override;
      end;
    procedure TAnimal.Speak; begin WriteLn(Name, ': ...') end;
    procedure TAnimal.Move; begin WriteLn(Name, ' walks') end;
    procedure TAnimal.Describe; begin WriteLn('an animal') end;
    procedure TDog.Speak; begin WriteLn(Name, ': woof') end;
    procedure TDog.Describe; begin WriteLn('a dog') end;
    procedure TCircle.Draw; begin WriteLn('circle drawn') end;
    procedure TCircle.Area; begin WriteLn('pi r squared') end;
    var
      A: TAnimal;
      S: TShape;
      I: IShape;
    begin
      A := TDog.Create();
      A.Name := 'rex';
      A.Speak();
      A.Move();
      A.Describe();
      TDog(A).Describe();
      A := TAnimal.Create();
      A.Name := 'generic';
      A.Speak();
      S := TCircle.Create();
      S.Draw();
      S.Area();
      I := TCircle.Create();
      I.Draw()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'rex: woof' + LE +
    'rex walks' + LE +
    'an animal' + LE +
    'a dog' + LE +
    'generic: ...' + LE +
    'circle drawn' + LE +
    'pi r squared' + LE +
    'circle drawn' + LE, 0);
end;

initialization
  RegisterTest(TE2EInheritTests);

end.
