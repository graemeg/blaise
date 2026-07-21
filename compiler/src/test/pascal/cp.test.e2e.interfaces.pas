{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.interfaces;

{ End-to-end tests for interfaces — compile + run on BOTH backends.  Grew
  out of the test-hardening sweep; the existing interface tests were
  IR/semantic-only, so the generated dispatch code was never exercised. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EInterfaceTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_BasicDispatch;
    procedure TestRun_MethodWithArgs;
    procedure TestRun_PolymorphicThroughInterfaceVar;
    procedure TestRun_ClassImplementsTwoInterfaces;
    { Passing a class instance directly to an interface-typed parameter
      (implicit class->interface narrowing at the call site). }
    procedure TestRun_GlobalClassVar_ToInterfaceParam;
    procedure TestRun_LocalClassVar_ToInterfaceParam;
    procedure TestRun_ConstructorResult_ToInterfaceParam;
    procedure TestRun_ProcInterfaceParam;
    { Interface inheritance: a derived-interface value is assignable where the
      base interface is expected (assignment, parameter, multi-level chain). }
    procedure TestRun_DerivedInterface_ToBaseVar;
    procedure TestRun_DerivedInterface_ToBaseParam;
    procedure TestRun_ThreeLevelInterfaceChain;
    { A class implementing a DERIVED interface, narrowed directly to a BASE
      interface (needs the class to emit an itab for the inherited base). }
    procedure TestRun_ClassImplDerived_ToBaseVar;
    procedure TestRun_ClassImplDerived_ToBaseParam;
    { A class that INHERITS an interface from its ancestor (the ancestor
      declares the interface; the descendant does not re-list it).  The
      descendant must be assignable/passable as that interface, dispatching to
      its own overrides and to inherited (non-overridden) methods alike
      (issue #130 bug3). }
    procedure TestRun_InheritedInterface_DescendantToVar;
    procedure TestRun_InheritedInterface_OverrideAndInheritedMethod;
    procedure TestRun_InheritedInterface_NonVirtualMethod;
    { An itab-dispatched method returning a RECORD.  Two ABI shapes:
      a memory-class record (has a managed field -> sret) and a register-class
      record (all-scalar, returned in registers).  Both must work when the
      result is ASSIGNED and when DISCARDED in statement position — the
      discarded statement and the assignment used to mis-handle the
      record-return ABI and corrupt memory (bug #5). }
    procedure TestRun_InterfaceMethod_ReturnsSretRecord;
    procedure TestRun_InterfaceMethod_ReturnsRegisterRecord;
    { A value-returning interface-method call whose receiver is an interface
      stored in a FIELD of Self (bare `FField.M()`), and one via a method-LOCAL
      interface variable copied from that field.  On the native backend both used
      to emit bogus bare _obj/_itab global operands (undefined-symbol link error
      under --linker external, or a call-through-garbage SIGSEGV) instead of
      loading the receiver's real fat pointer from Self+offset / the local slot. }
    procedure TestRun_InterfaceField_ValueReturn_InMethod;
    { Interface method with SIX parameters: Self + 6 args = 7 integer slots,
      one more than the System V registers.  The native itab-dispatch pop
      loop used to raise ("register index 6 out of range") instead of
      spilling the overflow slot to the stack.  Three dispatch shapes are
      covered: a plain interface-variable receiver, a class-FIELD receiver
      (a separate emitter), and a DISCARDED interface-returning call (sret
      shifts args to start at %rdx, overflowing one slot earlier). }
    procedure TestRun_InterfaceMethod_SixArgs_SpillsToStack;
    procedure TestRun_InterfaceFieldMethod_SixArgs_SpillsToStack;
    procedure TestRun_DiscardedIntfReturn_FiveArgs_SpillsToStack;
    { Float arguments through itab dispatch: the native backend used to have
      NO float classification at interface call sites — a float literal arg
      failed codegen outright and a float variable would have been routed
      into an integer register while the callee reads %xmm0.  Shapes:
      float-only, float mixed among integers, mixed WITH integer-slot
      overflow (>6 int slots + a float), and a class-field receiver. }
    procedure TestRun_InterfaceMethod_FloatArg;
    procedure TestRun_InterfaceMethod_MixedIntFloatArgs;
    procedure TestRun_InterfaceMethod_FloatArgAndIntSpill;
    procedure TestRun_InterfaceFieldMethod_FloatArg;
    { BUG-038: a nested routine using an INTERFACE variable captured from
      its enclosing routine — dispatch through the captured fat pointer
      (native used to emit bogus bare _obj/_itab globals; QBE failed to
      compile), and forwarding the captured interface as an argument. }
    procedure TestRun_NestedProc_DispatchOnCapturedInterface;
    procedure TestRun_NestedProc_PassesCapturedInterfaceOn;
    { BUG-052 F2: a class declares an interface method as virtual;abstract and a
      descendant overrides it.  The abstract class's itab slot points at the
      abort stub; the concrete descendant's itab dispatches to its override. }
    procedure TestRun_AbstractInterfaceMethod_ConcreteOverride;
    { BUG-20260720-qbe-dynarray-intf-elem-read: read a dyn-array-of-interface
      element as a method receiver, an assignment source, and a call argument. }
    procedure TestRun_DynArrayOfInterface_ElementRead;
  end;

implementation

const
  LE = #10;

procedure TE2EInterfaceTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-interfaces');
end;

const
  SrcBasic = '''
    program Prg;
    type
      IGreeter = interface function Greet: string; end;
      TEng = class(IGreeter) function Greet: string; begin Result := 'hello' end; end;
    var g: IGreeter;
    begin g := TEng.Create(); WriteLn(g.Greet()) end.
    ''';

  SrcArgs = '''
    program Prg;
    type
      ICalc = interface function Add(A, B: Integer): Integer; end;
      TCalc = class(ICalc) function Add(A, B: Integer): Integer; begin Result := A + B end; end;
    var c: ICalc;
    begin c := TCalc.Create(); WriteLn(c.Add(15, 27)) end.
    ''';

  SrcPolymorphic = '''
    program Prg;
    type
      IShape = interface function Area: Integer; end;
      TSquare = class(IShape) FS: Integer; function Area: Integer; begin Result := FS * FS end; end;
      TRect = class(IShape) FW, FH: Integer; function Area: Integer; begin Result := FW * FH end; end;
    var s: IShape; total: Integer;
    begin
      total := 0;
      s := TSquare.Create(); TSquare(s).FS := 4; total := total + s.Area();
      s := TRect.Create(); TRect(s).FW := 3; TRect(s).FH := 5; total := total + s.Area();
      WriteLn(total)
    end.
    ''';

  SrcTwoIntfs = '''
    program Prg;
    type
      IA = interface function NA: Integer; end;
      IB = interface function NB: Integer; end;
      TBoth = class(IA, IB) function NA: Integer; begin Result := 1 end; function NB: Integer; begin Result := 2 end; end;
    var a: IA; b: IB; o: TBoth;
    begin o := TBoth.Create(); a := o; b := o; WriteLn(a.NA() + b.NB()) end.
    ''';

  SrcGlobalToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    var t: TThing;
    begin t := TThing.Create(); WriteLn(Describe(t)) end.
    ''';

  SrcLocalToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    procedure Run; var t: TThing; begin t := TThing.Create(); WriteLn(Describe(t)) end;
    begin Run() end.
    ''';

  SrcCtorToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    begin WriteLn(Describe(TThing.Create())) end.
    ''';

  SrcProcParam = '''
    program Prg;
    type ILog = interface procedure Emit; end;
      TC = class(ILog) procedure Emit; begin WriteLn('emit') end; end;
    procedure Use(L: ILog); begin L.Emit() end;
    var c: TC;
    begin c := TC.Create(); Use(c) end.
    ''';

procedure TE2EInterfaceTests.TestRun_BasicDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBasic, 'hello' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_MethodWithArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArgs, '42' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_PolymorphicThroughInterfaceVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcPolymorphic, '31' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassImplementsTwoInterfaces;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTwoIntfs, '3' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_GlobalClassVar_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGlobalToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_LocalClassVar_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcLocalToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ConstructorResult_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCtorToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ProcInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcParam, 'emit' + LE, 0);
end;

const
  { IDog = interface(IAnimal): a derived-interface value is assignable where
    the base interface is expected. }
  SrcDerivedToBaseVar = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    var d: IDog; a: IAnimal;
    begin
      d := TDog.Create;
      a := d;
      WriteLn(a.Name());
      d := nil; a := nil
    end.
    ''';

  SrcDerivedToBaseParam = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    function Describe(a: IAnimal): string;
    begin Result := 'Animal: ' + a.Name() end;
    var d: IDog;
    begin
      d := TDog.Create;
      WriteLn(Describe(d));
      d := nil
    end.
    ''';

  SrcThreeLevelChain = '''
    program P;
    type
      IA = interface function A: Integer; end;
      IB = interface(IA) function B: Integer; end;
      IC = interface(IB) function C: Integer; end;
      TImpl = class(IC)
        function A: Integer; begin Result := 1 end;
        function B: Integer; begin Result := 2 end;
        function C: Integer; begin Result := 3 end;
      end;
    var c: IC; a: IA;
    begin
      c := TImpl.Create;
      a := c;
      WriteLn(a.A());
      c := nil; a := nil
    end.
    ''';

procedure TE2EInterfaceTests.TestRun_DerivedInterface_ToBaseVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDerivedToBaseVar, 'Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_DerivedInterface_ToBaseParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDerivedToBaseParam, 'Animal: Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ThreeLevelInterfaceChain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcThreeLevelChain, '1' + LE, 0);
end;

const
  { TDog implements IDog (derived); narrowing the INSTANCE directly to an
    IAnimal var/param needs the class to emit itab_TDog_IAnimal. }
  SrcClassImplDerivedToBaseVar = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    var a: IAnimal;
    begin
      a := TDog.Create;
      WriteLn(a.Name());
      a := nil
    end.
    ''';

  SrcClassImplDerivedToBaseParam = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    function Describe(a: IAnimal): string; begin Result := 'A:' + a.Name() end;
    begin
      WriteLn(Describe(TDog.Create))
    end.
    ''';

procedure TE2EInterfaceTests.TestRun_ClassImplDerived_ToBaseVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassImplDerivedToBaseVar, 'Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassImplDerived_ToBaseParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassImplDerivedToBaseParam, 'A:Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InheritedInterface_DescendantToVar;
const
  { TLoud inherits IGreeter from TPerson; assigning a TLoud to an IGreeter var
    must work and dispatch to TLoud's override (issue #130 bug3 — the repro). }
  Src = '''
    program P;
    type
      IGreeter = interface function Greet: string; end;
      TPerson = class(IGreeter) function Greet: string; virtual; end;
      TLoud   = class(TPerson)  function Greet: string; override; end;
    function TPerson.Greet: string; begin Result := 'hi' end;
    function TLoud.Greet: string;   begin Result := 'HI' end;
    var g: IGreeter;
    begin
      g := TPerson.Create; WriteLn(g.Greet());
      g := TLoud.Create;   WriteLn(g.Greet());
      g := nil
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hi' + LE + 'HI' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InheritedInterface_OverrideAndInheritedMethod;
const
  { Three-level chain through an interface parameter: each level's itab must
    resolve overridden methods to the level's own body and NON-overridden
    methods to the inherited ancestor body (Who is never overridden). }
  Src = '''
    program P;
    type
      IGreeter = interface
        function Greet: string;
        function Who: string;
      end;
      TPerson = class(IGreeter)
        function Greet: string; virtual;
        function Who: string; virtual;
      end;
      TLoud     = class(TPerson) function Greet: string; override; end;
      TVeryLoud = class(TLoud)   function Greet: string; override; end;
    function TPerson.Greet: string; begin Result := 'hi' end;
    function TPerson.Who: string;   begin Result := 'person' end;
    function TLoud.Greet: string;     begin Result := 'HI' end;
    function TVeryLoud.Greet: string; begin Result := 'HI!!!' end;
    procedure Use(g: IGreeter);
    begin WriteLn(g.Greet(), ' / ', g.Who()) end;
    var per: TPerson; lou: TLoud; vl: TVeryLoud;
    begin
      per := TPerson.Create; Use(per); per.Free();
      lou := TLoud.Create;   Use(lou); lou.Free();
      vl := TVeryLoud.Create; Use(vl); vl.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'hi / person' + LE + 'HI / person' + LE + 'HI!!! / person' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InheritedInterface_NonVirtualMethod;
const
  { Regression (issue #130 bug3): a NON-virtual interface method inherited by a
    descendant.  A non-virtual method gets no vtable slot, so the itab method ref
    cannot be resolved via the vtable; the descendant's itab used to name
    $TDerived_Hello (which does not exist) instead of the declaring ancestor's
    $TBase_Hello, causing an "undefined symbol"/link error.  The earlier
    inherited-interface tests only exercised VIRTUAL methods, which DO have
    vtable slots, so this path went uncovered.  Both backends must now link+run. }
  Src = '''
    program P;
    type
      IBase = interface procedure Hello; end;
      TBase = class(IBase) procedure Hello; end;
      TDerived = class(TBase) end;
    procedure TBase.Hello; begin WriteLn('hello') end;
    procedure Use(g: IBase); begin g.Hello() end;
    var d: TDerived; i: IBase;
    begin
      d := TDerived.Create;
      i := d;        // assignment to interface
      i.Hello();
      Use(d);        // parameter passing
      d.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hello' + LE + 'hello' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_ReturnsSretRecord;
const
  { TRect has a managed (string) field, so ClassifyRecordReturn => sret. }
  Src = '''
    program P;
    type
      TRect = record Name: string; N: Integer; end;
      IShape = interface
        function MakeRect(AN: Integer): TRect;
      end;
      TShape = class(IShape)
        function MakeRect(AN: Integer): TRect;
      end;
    function TShape.MakeRect(AN: Integer): TRect;
    begin
      Result.Name := 'r';
      Result.N := AN;
      WriteLn('callee ', AN)
    end;
    var
      M: IShape;
      R: TRect;
    begin
      M := TShape.Create();
      R := M.MakeRect(5);       { assigned sret record return }
      WriteLn('assigned ', R.N);
      M.MakeRect(7)             { discarded sret record return }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'callee 5' + LE + 'assigned 5' + LE + 'callee 7' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_ReturnsRegisterRecord;
const
  { TPt is all-scalar, so ClassifyRecordReturn => a register-class return
    (no sret buffer); the itab dispatch must capture the register result. }
  Src = '''
    program P;
    type
      TPt = record X, Y: Integer; end;
      IShape = interface
        function MakePt(AN: Integer): TPt;
      end;
      TShape = class(IShape)
        function MakePt(AN: Integer): TPt;
      end;
    function TShape.MakePt(AN: Integer): TPt;
    begin
      Result.X := AN;
      Result.Y := AN * 2;
      WriteLn('callee ', AN)
    end;
    var
      M: IShape;
      R: TPt;
    begin
      M := TShape.Create();
      R := M.MakePt(5);         { assigned register-class record return }
      WriteLn('assigned ', R.X, ' ', R.Y);
      M.MakePt(9)               { discarded register-class record return }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'callee 5' + LE + 'assigned 5 10' + LE + 'callee 9' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceField_ValueReturn_InMethod;
const
  { CallField dispatches on the interface FIELD (FT.V()) inside a method;
    CallLocal copies the field into a method-LOCAL interface var first (L := FT)
    then dispatches on it.  Both are value-returning; on native they used to
    resolve the receiver via bogus bare _obj/_itab labels. }
  Src = '''
    program P;
    type
      IThing = interface function V: Integer; end;
      TThing = class(IThing) function V: Integer; begin Result := 42 end; end;
      THold = class
      private
        FT: IThing;
      public
        procedure SetT(t: IThing);
        function CallField: Integer;
        function CallLocal: Integer;
      end;
    procedure THold.SetT(t: IThing); begin FT := t end;
    function THold.CallField: Integer; begin Result := FT.V() end;
    function THold.CallLocal: Integer;
    var L: IThing;
    begin L := FT; Result := L.V() end;
    var H: THold; T: TThing;
    begin
      T := TThing.Create();
      H := THold.Create();
      H.SetT(T);
      WriteLn('CallField=', H.CallField());
      WriteLn('CallLocal=', H.CallLocal())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'CallField=42' + LE + 'CallLocal=42' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_SixArgs_SpillsToStack;
const
  Src = '''
    program p;
    type
      ISink = interface
        function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
      end;
      TSink = class(TObject, ISink)
      public
        function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
      end;
    function TSink.Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
    begin
      Result := Length(AName) + AA + AB * 10 + AC * 100 + AD * 1000 + AE * 10000
    end;
    var S: ISink;
    begin
      S := TSink.Create();
      { 3 + 1 + 20 + 300 + 4000 + 50000 = 54324 }
      WriteLn(S.Take('abc', 1, 2, 3, 4, 5))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '54324' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceFieldMethod_SixArgs_SpillsToStack;
const
  Src = '''
    program p;
    type
      ISink = interface
        function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
      end;
      TSink = class(TObject, ISink)
      public
        function Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
      end;
      THold = class
      private
        FS: ISink;
      public
        procedure Bind(s: ISink);
        function Call: Integer;
      end;
    function TSink.Take(const AName: string; AA, AB, AC, AD, AE: Integer): Integer;
    begin
      Result := Length(AName) + AA + AB * 10 + AC * 100 + AD * 1000 + AE * 10000
    end;
    procedure THold.Bind(s: ISink); begin FS := s end;
    function THold.Call: Integer;
    begin
      Result := FS.Take('abcd', 5, 4, 3, 2, 1)
    end;
    var H: THold;
    begin
      H := THold.Create();
      H.Bind(TSink.Create());
      { 4 + 5 + 40 + 300 + 2000 + 10000 = 12349 }
      WriteLn(H.Call())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12349' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_DiscardedIntfReturn_FiveArgs_SpillsToStack;
const
  { A DISCARDED interface-returning itab call uses the sret convention:
    %rdi = buffer, %rsi = Self, visible args from %rdx — so five args
    already need seven integer slots and must spill one. }
  Src = '''
    program p;
    type
      ISink = interface
        function Note(AA, AB, AC, AD, AE: Integer): ISink;
      end;
      TSink = class(TObject, ISink)
      public
        function Note(AA, AB, AC, AD, AE: Integer): ISink;
      end;
    function TSink.Note(AA, AB, AC, AD, AE: Integer): ISink;
    begin
      WriteLn(AA + AB * 10 + AC * 100 + AD * 1000 + AE * 10000);
      Result := Self
    end;
    var S: ISink;
    begin
      S := TSink.Create();
      { statement position: the returned interface is discarded }
      S.Note(5, 4, 3, 2, 1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12345' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_FloatArg;
const
  Src = '''
    program p;
    type
      IC = interface
        function AddHalf(X: Double): Double;
      end;
      TC = class(TObject, IC)
      public
        function AddHalf(X: Double): Double;
      end;
    function TC.AddHalf(X: Double): Double;
    begin
      Result := X + 0.5
    end;
    var
      C: IC;
      V: Double;
    begin
      C := TC.Create();
      V := 1.5;
      WriteLn(C.AddHalf(1.5) = 2.0);   { literal arg }
      WriteLn(C.AddHalf(V) = 2.0)      { variable arg }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_MixedIntFloatArgs;
const
  { The float sits BETWEEN integer args: integer slots must keep consuming
    %rsi.. across it while the float takes %xmm0 (independent sequences). }
  Src = '''
    program p;
    type
      IM = interface
        function Mix(A: Integer; X: Double; B: Integer): Integer;
      end;
      TM = class(TObject, IM)
      public
        function Mix(A: Integer; X: Double; B: Integer): Integer;
      end;
    function TM.Mix(A: Integer; X: Double; B: Integer): Integer;
    begin
      Result := A * 100 + Trunc(X * 10.0) + B
    end;
    var M: IM;
    begin
      M := TM.Create();
      { 700 + 25 + 9 = 734 }
      WriteLn(M.Mix(7, 2.5, 9))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '734' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_FloatArgAndIntSpill;
const
  { Self + string + five Integers = 7 integer slots (one spills) while the
    Double rides in %xmm0 — spill relocation must skip the float slot. }
  Src = '''
    program p;
    type
      IS2 = interface
        function Take(const AName: string; AA, AB, AC, AD: Integer;
                      X: Double; AE: Integer): Integer;
      end;
      TS = class(TObject, IS2)
      public
        function Take(const AName: string; AA, AB, AC, AD: Integer;
                      X: Double; AE: Integer): Integer;
      end;
    function TS.Take(const AName: string; AA, AB, AC, AD: Integer;
                     X: Double; AE: Integer): Integer;
    begin
      Result := Length(AName) + AA + AB * 10 + AC * 100 + AD * 1000
        + Trunc(X) * 10000 + AE * 100000
    end;
    var S: IS2;
    begin
      S := TS.Create();
      { 3 + 1 + 20 + 300 + 4000 + 70000 + 500000 = 574324 }
      WriteLn(S.Take('abc', 1, 2, 3, 4, 7.0, 5))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '574324' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceFieldMethod_FloatArg;
const
  Src = '''
    program p;
    type
      IC = interface
        function Scale(X: Double; N: Integer): Double;
      end;
      TC = class(TObject, IC)
      public
        function Scale(X: Double; N: Integer): Double;
      end;
      THold = class
      private
        FC: IC;
      public
        procedure Bind(c: IC);
        function Call: Double;
      end;
    function TC.Scale(X: Double; N: Integer): Double;
    begin
      Result := X * N
    end;
    procedure THold.Bind(c: IC); begin FC := c end;
    function THold.Call: Double;
    begin
      Result := FC.Scale(2.5, 4)
    end;
    var H: THold;
    begin
      H := THold.Create();
      H.Bind(TC.Create());
      WriteLn(H.Call() = 10.0)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_NestedProc_DispatchOnCapturedInterface;
const
  Src = '''
    program p;
    type
      IThing = interface
        function V: Integer;
      end;
      TThing = class(TObject, IThing)
      public
        function V: Integer;
      end;
    function TThing.V: Integer;
    begin
      Result := 42
    end;
    procedure Run;
    var
      T: IThing;
      N: Integer;
      procedure Inner;
      begin
        WriteLn(T.V());      { statement position }
        N := T.V() + 1       { expression position }
      end;
    begin
      T := TThing.Create();
      N := 0;
      Inner();
      WriteLn(N)
    end;
    begin
      Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '42' + LE + '43' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_NestedProc_PassesCapturedInterfaceOn;
const
  Src = '''
    program p;
    type
      IThing = interface
        function V: Integer;
      end;
      TThing = class(TObject, IThing)
      public
        function V: Integer;
      end;
    function TThing.V: Integer;
    begin
      Result := 7
    end;
    procedure Show(AThing: IThing);
    begin
      WriteLn(AThing.V())
    end;
    procedure Run;
    var
      T: IThing;
      procedure Inner;
      begin
        Show(T)      { captured interface forwarded as an argument }
      end;
    begin
      T := TThing.Create();
      Inner()
    end;
    begin
      Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_AbstractInterfaceMethod_ConcreteOverride;
const Src = '''
    program P;
    type
      IShape = interface
        function Area: Integer;
      end;
      TBase = class(TObject, IShape)
        function Area: Integer; virtual; abstract;
      end;
      TSquare = class(TBase)
        Side: Integer;
        function Area: Integer; override;
      end;
    function TSquare.Area: Integer;
    begin Result := Side * Side end;
    var
      S: TSquare;
      Sh: IShape;
    begin
      S := TSquare.Create();
      S.Side := 4;
      Sh := S;
      WriteLn(Sh.Area())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { the abstract base's IShape itab slot points at the abort stub; the concrete
    TSquare's dispatches to its override — 4*4=16 }
  AssertRunsOnAll(Src, '16' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_DynArrayOfInterface_ElementRead;
const
  Src =
    '''
    program Prg;
    type
      IGreet = interface function Name: string; end;
      TGreet = class(IGreet) FName: string; function Name: string; begin Result := FName end; end;
    procedure Use(G: IGreet);
    begin WriteLn('arg=', G.Name()) end;
    var Arr: array of IGreet; X: IGreet; G: TGreet;
    begin
      SetLength(Arr, 3);
      G := TGreet.Create(); G.FName := 'aaa'; Arr[0] := G;
      G := TGreet.Create(); G.FName := 'bbb'; Arr[1] := G;
      G := TGreet.Create(); G.FName := 'ccc'; Arr[2] := G;
      WriteLn('recv=', Arr[1].Name());   { method receiver }
      X := Arr[2];                        { assignment source }
      WriteLn('assign=', X.Name());
      Use(Arr[0])                         { call argument }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'recv=bbb' + LE + 'assign=ccc' + LE + 'arg=aaa' + LE, 0);
end;

initialization
  RegisterTest(TE2EInterfaceTests);

end.
