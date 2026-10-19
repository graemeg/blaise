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
    { interface and metaclass fields read off a call result: the value
      outlives the transient object, which is freed once, after the statement }
    procedure TestRun_IntfAndMetaclassFieldOfCallResult;
    { a procedural field whose result comes back through the hidden result
      buffer (an interface, a record over 16 bytes), called on an explicit
      receiver and on implicit Self, into every consumer }
    procedure TestRun_ProcFieldCall_AggregateResult;
    procedure TestRun_ProcFieldCall_AggregateResult_DiscardedAndRepeated;
    { Obj as IFoo into every consumer: a field of Self, a var / out
      parameter, Result, an element, an argument, a receiver; a borrowed
      and an owned source; a failed cast in argument position raises }
    procedure TestRun_AsCast_IntoEveryConsumer;
    { interface values read in place -- an element of a field of Self, a
      dynamic-array element, P^ -- into every consumer, and interface
      arguments that spill to the stack (a class value among them) }
    procedure TestRun_InPlaceIntfSources_IntoEveryConsumer;
    { IFoo(X) as a checked conversion: from a class value (borrowed and
      owned) and a descendant interface, into every consumer }
    procedure TestRun_InterfaceCast_IntoEveryConsumer;
    { TGreet(MakeI()).X: the call's owned reference is released -- the shared
      object goes when its last real holder lets go }
    procedure TestRun_ClassCastOfInterfaceCall_ReleasesTheCallRef;
    { Interface (and closure) values read through a class PROPERTY getter, a
      static var, a static property, and as chained call receivers
      (C.PT.Name(), TC.ST.Name(), J.Next.Next.Name()).  arm64 refused them;
      the x86-64 compiler segfaulted on the getter forms. }
    procedure TestRun_InterfaceFromGettersAndStaticMembers;
    procedure TestRun_InterfaceProperty_ThroughRecordField;
    { Interface properties of every kind -- indexed and plain, Integer,
      Double, Single and string, read and written, on a variable and on a
      chained receiver.  An indexed read or write dropped the index on
      both backends (arm64 crashed, x86-64 failed to compile), and a float
      property crashed the x86-64 compiler. }
    procedure TestRun_InterfaceProperty_EveryKind;
    procedure TestRun_Interfaces_Combined;
    procedure TestRun_BasicDispatch;
    { arguments classified by the DECLARED parameter: Integer to Double,
      Double to Single, Int64 stack slots, ten doubles, a const string }
    procedure TestRun_IntfCall_ArgsByDeclaredParams;
    { a record-returning interface method taking float arguments, on every
      receiver form including a call result }
    procedure TestRun_IntfRecordReturn_FloatArgs_AllReceivers;
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
    { An interface method returning a record, through every receiver and
      destination: a global, a field of Self, a var param, reassignment over
      a managed value, discarded, and as a by-const argument. }
    procedure TestRun_InterfaceMethod_RecordReturn_AllForms;
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
    { arm64 leg 40: IntfVar := Obj.Method() where a class-receiver method
      returns an interface — the fat pointer round-trips and dispatches. }
    procedure TestRun_InterfaceAssign_FromMethodResult;
    { Class downcast of an interface ARRAY ELEMENT used as a field-write
      receiver: QBE treated the element's fat-pointer ADDRESS as the object
      base, silently storing into the wrong memory
      (BUG-20260721-qbe-downcast-intf-elem-field-write). }
    procedure TestRun_ClassDowncastOfIntfElement_FieldWrite;
    { Class downcast of the remaining interface operand shapes: implicit-Self
      interface field, var-param interface, interface-returning call result,
      interface-returning METHOD-call result, sret interface Result, and a
      captured interface local inside a nested routine.  QBE's old ident
      special case emitted loads from nonexistent %_var_X_obj slots (fixed via
      EmitInterfaceExprPair); native's ident-only special case crashed on all
      of these shapes (BUG-20260722-native-downcast-intf-nonslot-shapes). }
    procedure TestRun_ClassDowncastOfIntf_IdentShapes;
    { Interface elements of ARRAY FIELDS (H.FArr[0] — a TFieldAccessExpr with
      IsArrayAccess, not a subscript node): the read arms treated the field
      slot as the pair base with no index scaling (SIGSEGV both backends),
      and the element STORE wrote only the obj half (garbage itab)
      (BUG-20260721-fieldaccess-intf-array-elem-read). }
    procedure TestRun_InterfaceElem_OfArrayField;
    { Interface element of an array field reached through a NESTED record chain
      (O.B.Arr[0].Hi()): the QBE chained-base read arm (FldAccess.Base <> nil)
      had drifted from the leaf arm and only returned the element address for
      tyRecord — so an interface element was loaded as an 8-byte scalar and
      dispatch/read crashed (QBE only; native uniform base handling was correct)
      (BUG-20260723-qbe-intf-nested-chain-array-elem). }
    procedure TestRun_InterfaceElem_OfNestedFieldChainArray;

    { Interface element read through an INDEXED PROPERTY (TList<IFoo>[i]) }
    procedure TestRun_InterfaceElem_ViaIndexedProperty_ToLocal;
    procedure TestRun_InterfaceElem_ViaIndexedProperty_ToResult;

    { A PROGRAM-level interface (or metaclass) global whose first use is a var
      argument.  x86-64 registered program globals of these kinds only on an
      assignment, so this one was never defined: the call linked against an
      undefined <Name>_obj and the program died with no output. }
    procedure TestRun_ProgramGlobals_ReachedOnlyThroughVarArg;
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

procedure TE2EInterfaceTests.TestRun_InterfaceMethod_RecordReturn_AllForms;
const
  Src = '''
    program P;
    type
      TRect = record Name: string; N: Integer; end;
      TPt = record X, Y: Integer; end;
      IShape = interface
        function MakeRect(AN: Integer): TRect;
        function MakePt(AN: Integer): TPt;
      end;
      TShape = class(IShape)
        function MakeRect(AN: Integer): TRect;
        function MakePt(AN: Integer): TPt;
      end;
      TUser = class
        FS: IShape;
        procedure Go();
      end;
    function TShape.MakeRect(AN: Integer): TRect;
    begin
      Result.Name := 'r' + IntToStr(AN);
      Result.N := AN
    end;
    function TShape.MakePt(AN: Integer): TPt;
    begin
      Result.X := AN;
      Result.Y := AN * 2
    end;
    procedure Show(const R: TRect);
    begin
      WriteLn('show ', R.Name, ' ', R.N)
    end;
    procedure TUser.Go();
    var R: TRect; Q: TPt;
    begin
      R := FS.MakeRect(3);
      Q := FS.MakePt(4);
      WriteLn(R.Name, ' ', Q.Y);
      FS.MakeRect(5);
      FS.MakePt(6)
    end;
    procedure ByVar(var S: IShape);
    var R: TRect;
    begin
      R := S.MakeRect(8);
      WriteLn(R.Name);
      S.MakeRect(9)
    end;
    var M: IShape; R: TRect; U: TUser;
    begin
      M := TShape.Create();
      R := M.MakeRect(1);
      R := M.MakeRect(2);
      WriteLn(R.Name, ' ', R.N);
      Show(M.MakeRect(7));
      U := TUser.Create();
      U.FS := M;
      U.Go();
      ByVar(M);
      U.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'r2 2' + LE + 'show r7 7' + LE + 'r3 8' + LE + 'r8' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
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

procedure TE2EInterfaceTests.TestRun_InterfaceAssign_FromMethodResult;
const
  Src = '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      THi = class(TObject, IGreeter)
        function Greet: Integer;
        function GetSelf: IGreeter;
      end;
    function THi.Greet: Integer; begin Result := 7 end;
    function THi.GetSelf: IGreeter; begin Result := Self end;
    var H: THi; G: IGreeter;
    begin
      H := THi.Create();
      G := H.GetSelf();
      WriteLn(G.Greet());
      G := nil;
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassDowncastOfIntfElement_FieldWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      IGreet = interface
        function Name(): string;
      end;
      TGreet = class(TObject, IGreet)
      public
        FName: string;
        function Name(): string;
      end;
    function TGreet.Name(): string;
    begin
      Result := FName
    end;
    var
      Arr: array of IGreet;
      SA: array[0..0] of IGreet;
    begin
      SetLength(Arr, 1);
      Arr[0] := TGreet.Create();
      TGreet(Arr[0]).FName := 'zzz';
      WriteLn(Arr[0].Name());
      SA[0] := TGreet.Create();
      TGreet(SA[0]).FName := 'yyy';
      WriteLn(SA[0].Name());
      WriteLn(TGreet(Arr[0]).FName)
    end.
    ''', 'zzz' + LE + 'yyy' + LE + 'zzz' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassDowncastOfIntf_IdentShapes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      IGreet = interface
        function Name(): string;
      end;
      TGreet = class(TObject, IGreet)
      public
        FName: string;
        function Name(): string;
      end;
      THolder = class(TObject)
      public
        FI: IGreet;
        procedure Poke();
        function GetI(): IGreet;
      end;
    function TGreet.Name(): string;
    begin
      Result := FName
    end;
    procedure THolder.Poke();
    begin
      TGreet(FI).FName := 'self'
    end;
    function THolder.GetI(): IGreet;
    begin
      Result := FI
    end;
    var
      G: IGreet;
      H: THolder;
    function MakeI(): IGreet;
    begin
      Result := G
    end;
    procedure PokeVar(var I: IGreet);
    begin
      TGreet(I).FName := 'varparam'
    end;
    function MakeAndPoke(): IGreet;
    begin
      Result := TGreet.Create();
      TGreet(Result).FName := 'sretresult'
    end;
    procedure PokeCaptured();
    var
      I: IGreet;
      procedure Inner();
      begin
        TGreet(I).FName := 'captured'
      end;
    begin
      I := TGreet.Create();
      Inner();
      WriteLn(I.Name())
    end;
    begin
      H := THolder.Create();
      H.FI := TGreet.Create();
      H.Poke();
      WriteLn(H.FI.Name());
      G := TGreet.Create();
      PokeVar(G);
      WriteLn(G.Name());
      TGreet(MakeI()).FName := 'call';
      WriteLn(TGreet(MakeI()).FName);
      TGreet(H.GetI()).FName := 'mcall';
      WriteLn(H.FI.Name());
      WriteLn(MakeAndPoke().Name());
      PokeCaptured()
    end.
    ''', 'self' + LE + 'varparam' + LE + 'call' + LE + 'mcall' + LE +
         'sretresult' + LE + 'captured' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceElem_OfArrayField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      IGreet = interface
        function Hi(): Integer;
      end;
      TG = class(TObject, IGreet)
      public
        FN: Integer;
        function Hi(): Integer;
      end;
      THold = class
      public
        FArr: array of IGreet;
        FSt: array[0..1] of IGreet;
        function ProbeSelf(): Integer;
      end;
    function TG.Hi(): Integer;
    begin
      Result := FN
    end;
    function THold.ProbeSelf(): Integer;
    begin
      Result := FArr[0].Hi()         { implicit-Self field element read }
    end;
    function Mk(N: Integer): IGreet;
    var G: TG;
    begin
      G := TG.Create();
      G.FN := N;
      Result := G
    end;
    procedure TakeIntf(AG: IGreet);
    begin
      WriteLn(AG.Hi())
    end;
    var
      H: THold;
      G2: IGreet;
      GC: TG;
    function MkGrow(N: Integer): IGreet;
    begin
      { reallocates the SAME dyn-array field the caller stores into }
      SetLength(H.FArr, 4);
      Result := Mk(N)
    end;
    begin
      H := THold.Create();
      SetLength(H.FArr, 2);
      H.FArr[0] := Mk(3);            { interface-call RHS store }
      GC := TG.Create();
      GC.FN := 9;
      H.FArr[1] := GC;               { class RHS store (obj + static itab) }
      H.FSt[0] := Mk(4);             { static-array field element store }
      WriteLn(H.FArr[0].Hi());       { method receiver }
      WriteLn(H.FArr[1].Hi());
      G2 := H.FArr[0];               { assignment RHS }
      WriteLn(G2.Hi());
      WriteLn(H.FSt[0].Hi());
      WriteLn(H.ProbeSelf());
      TakeIntf(H.FArr[0]);           { interface-param arg pass, dyn }
      TakeIntf(H.FSt[0]);            { interface-param arg pass, static }
      WriteLn(TG(H.FArr[0]).FN);     { class downcast of the element }
      if H.FArr[0] <> nil then       { nil compare reads the obj half }
        WriteLn('nn');
      H.FArr[0] := nil;
      if H.FArr[0] = nil then
        WriteLn('nil');
      H.FArr[1] := MkGrow(7);        { RHS reallocs the field mid-store —
                                       value-first ordering required }
      WriteLn(H.FArr[1].Hi())
    end.
    ''', '3' + LE + '9' + LE + '3' + LE + '4' + LE + '3' + LE +
         '3' + LE + '4' + LE + '3' + LE + 'nn' + LE + 'nil' + LE +
         '7' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceElem_OfNestedFieldChainArray;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      IGreet = interface
        function Hi(): Integer;
      end;
      TG = class(TObject, IGreet)
      public
        FN: Integer;
        function Hi(): Integer;
      end;
      TInner = record
        Arr: array[0..1] of IGreet;
        DArr: array of IGreet;
      end;
      TOuter = record Tag: Int64; B: TInner; end;
    function TG.Hi(): Integer;
    begin
      Result := FN
    end;
    function Mk(N: Integer): IGreet;
    var G: TG;
    begin
      G := TG.Create();
      G.FN := N;
      Result := G
    end;
    var
      O: TOuter;
      G2: IGreet;
    begin
      O.Tag := 1;
      O.B.Arr[0] := Mk(42);          { nested-chain store }
      O.B.Arr[1] := Mk(7);
      WriteLn(O.B.Arr[0].Hi());      { nested-chain method receiver }
      G2 := O.B.Arr[1];              { nested-chain assignment RHS }
      WriteLn(G2.Hi());
      SetLength(O.B.DArr, 2);        { same shapes over a DYN array field —
                                       the chained-base arm's dyn and static
                                       exit conditions drifted independently }
      O.B.DArr[0] := Mk(11);
      O.B.DArr[1] := Mk(13);
      WriteLn(O.B.DArr[0].Hi());
      G2 := O.B.DArr[1];
      WriteLn(G2.Hi())
    end.
    ''', '42' + LE + '7' + LE + '11' + LE + '13' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceElem_ViaIndexedProperty_ToLocal;
begin
  { `V := List[I]` where the element type is an INTERFACE.  The existing
    interface-element arms all assume an element ADDRESS (static/dyn/open
    arrays, record fields), but an indexed property's getter returns the fat
    pair BY VALUE through sret, so this fell to the fail-loud else on both
    backends: QBE "Unsupported interface expression form ... TStringSubscript
    Expr", native "unsupported interface-field assignment RHS".  Reached by
    any TList<IFoo> — found porting tools/blaise-guard. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program P;
    uses SysUtils, Generics.Collections;
    type
      IThing = interface
        function Name: string;
      end;
      TThing = class(IThing)
        FN: string;
        function Name: string;
      end;
    function TThing.Name: string; begin Result := FN end;
    var L: TList<IThing>; V: IThing; T: TThing;
    begin
      L := TList<IThing>.Create();
      T := TThing.Create(); T.FN := 'alpha';
      L.Add(T);
      V := L[0];
      WriteLn(V.Name())
    end.
    ''', 'alpha' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceElem_ViaIndexedProperty_ToResult;
begin
  { The same read as a function RESULT — a separate codegen path from the
    local-variable case (sret Result assignment vs interface field slot), so
    both need pinning. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program P;
    uses SysUtils, Generics.Collections;
    type
      IThing = interface
        function Name: string;
      end;
      TThing = class(IThing)
        FN: string;
        function Name: string;
      end;
    function TThing.Name: string; begin Result := FN end;
    var GL: TList<IThing>;
    function Pick(I: Integer): IThing;
    begin
      Result := GL[I]
    end;
    var T: TThing;
    begin
      GL := TList<IThing>.Create();
      T := TThing.Create(); T.FN := 'beta';
      GL.Add(T);
      WriteLn(Pick(0).Name())
    end.
    ''', 'beta' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_Interfaces_Combined;
const
  {
    Interfaces end to end, leak-checked: the (obj, itab) pair in locals,
    array elements and a record field (SizeOf 24 -- the pair is 16 bytes),
    dispatch through each; is / as / Supports (two- and three-argument);
    interface arguments from an identifier, an as-cast and a method
    parameter; property read and write; nil compares on a local and on an interface Result; an
    interface-returning method assigned and discarded; a record and an out
    string through itab dispatch; and release timing -- reassigning the last
    reference destroys at once, Obj := nil and D := nil release theirs at
    once, and scope exit releases the last one. }
  Src = '''
    program P;
    type
      TOpts = record
        A, B, C: Integer;
        Name: string;
      end;
      IFoo = interface
        function GetVal: Integer;
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        property Value: Integer read GetValue write SetValue;
        procedure Configure(const O: TOpts);
        procedure Describe(out S: string);
        function Again: IFoo;
      end;
      IBar = interface
        function Bar: string;
      end;
      TFoo = class(TObject, IFoo)
        FVal: Integer;
        Tag: string;
        constructor Create(const ATag: string; AVal: Integer);
        destructor Destroy; override;
        function GetVal: Integer;
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        procedure Configure(const O: TOpts);
        procedure Describe(out S: string);
        function Again: IFoo;
      end;
      TPlain = class
      end;
      TRec = record
        F: IFoo;
        Tag: Integer;
      end;
      THelper = class
        procedure Use(I: IFoo);
      end;
    constructor TFoo.Create(const ATag: string; AVal: Integer);
    begin
      Tag := ATag;
      FVal := AVal
    end;
    destructor TFoo.Destroy;
    begin
      WriteLn('destroy ', Tag);
      inherited Destroy()
    end;
    function TFoo.GetVal(): Integer; begin Result := FVal end;
    function TFoo.GetValue(): Integer; begin Result := FVal * 10 end;
    procedure TFoo.SetValue(AValue: Integer); begin FVal := AValue end;
    procedure TFoo.Configure(const O: TOpts);
    begin
      FVal := O.A + O.B + O.C;
      Tag := Tag + '/' + O.Name
    end;
    procedure TFoo.Describe(out S: string);
    begin
      S := 'desc-' + Tag
    end;
    function TFoo.Again: IFoo; begin Result := Self end;
    procedure THelper.Use(I: IFoo);
    begin
      WriteLn('helper ', I.GetVal())
    end;
    procedure UseIntf(I: IFoo);
    begin
      WriteLn('use ', I.GetVal())
    end;
    function MaybeFoo(Make: Boolean): IFoo;
    begin
      if Make then Result := TFoo.Create('m', 4);
      if Result = nil then WriteLn('result nil') else WriteLn('result set')
    end;
    procedure Run;
    var
      F, G, W: IFoo; D: IFoo; Arr: array[0..1] of IFoo; Obj, Pl: TObject;
      R: TRec; H: THelper; O: TOpts; S: string; B: Boolean;
    begin
      F := TFoo.Create('a', 1);
      WriteLn(F.GetVal());
      Arr[0] := F;
      Arr[1] := TFoo.Create('b', 2);
      WriteLn(Arr[1].GetVal(), ' ', Arr[0].GetVal());
      G := Arr[1];
      Arr[1] := nil;
      WriteLn('g ', G.GetVal());
      Obj := TFoo.Create('c', 3);
      Pl := TPlain.Create();
      WriteLn(Obj is IFoo, ' ', Pl is IFoo, ' ', Supports(Obj, IFoo), ' ', Supports(Pl, IFoo));
      B := Supports(Obj, IFoo, W);
      WriteLn(B, ' ', W.GetVal());
      UseIntf(Obj as IFoo);
      UseIntf(F);
      H := THelper.Create();
      H.Use(G);
      R.F := F;
      R.Tag := 5;
      WriteLn(SizeOf(TRec), ' ', R.Tag, ' ', R.F.GetVal());
      F.Value := 13;
      WriteLn(F.Value);
      if D = nil then WriteLn('local nil');
      D := MaybeFoo(False);
      D := MaybeFoo(True);
      W := F.Again();
      WriteLn('again ', W.GetVal());
      F.Again();
      O.A := 1; O.B := 2; O.C := 3; O.Name := 'cfg';
      G.Configure(O);
      G.Describe(S);
      WriteLn(G.GetVal(), ' ', S);
      G := F;
      WriteLn('reassigned');
      H.Free();
      Pl.Free();
      Obj := nil;
      D := nil
    end;
    begin
      Run();
      WriteLn('done')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1' + LE +
    '2 1' + LE +
    'g 2' + LE +
    'True False True False' + LE +
    'True 3' + LE +
    'use 3' + LE +
    'use 1' + LE +
    'helper 2' + LE +
    '24 5 1' + LE +
    '130' + LE +
    'local nil' + LE +
    'result nil' + LE +
    'result set' + LE +
    'again 13' + LE +
    '6 desc-b/cfg' + LE +
    'destroy b/cfg' + LE +
    'reassigned' + LE +
    'destroy c' + LE +
    'destroy m' + LE +
    'destroy a' + LE +
    'done' + LE, 0);
  AssertLeakFreeOnAll(Src, 'reassigned');
end;

procedure TE2EInterfaceTests.TestRun_InterfaceProperty_ThroughRecordField;
const
  {
    An interface property read through a record field (R.F.Value) dispatches
    the getter through the field's itab, like a method call through the same
    chain.  The semantic pass used to reject it ("requires a record or class
    base, got 'IFoo'").  Native only: the QBE backend, due for removal, does
    not support the chained receiver. }
  Src = '''
    program P;
    type
      IFoo = interface
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        property Value: Integer read GetValue write SetValue;
      end;
      TFoo = class(TObject, IFoo)
        FVal: Integer;
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
      end;
      TRec = record
        F: IFoo;
        Tag: Integer;
      end;
      THolder = class
        R: TRec;
      end;
    function TFoo.GetValue(): Integer; begin Result := FVal * 10 end;
    procedure TFoo.SetValue(AValue: Integer); begin FVal := AValue end;
    var R: TRec; H: THolder;
    begin
      R.F := TFoo.Create();
      R.F.SetValue(4);
      WriteLn(R.F.Value);
      H := THolder.Create();
      H.R.F := R.F;
      H.R.F.SetValue(7);
      WriteLn(H.R.F.Value, ' ', R.F.Value);
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '40' + LE +
    '70 70' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceProperty_EveryKind;
const
  Src = '''
    program P;
    type
      IV = interface
        function GetN(I: Integer): Integer;
        procedure SetN(I: Integer; V: Integer);
        function GetD(I: Integer): Double;
        procedure SetD(I: Integer; V: Double);
        function GetS(): Single;
        procedure SetS(V: Single);
        function GetR(): Double;
        procedure SetR(V: Double);
        function GetT(const K: string): string;
        procedure SetT(const K: string; const V: string);
        property Ns[I: Integer]: Integer read GetN write SetN;
        property Ds[I: Integer]: Double read GetD write SetD;
        property S: Single read GetS write SetS;
        property R: Double read GetR write SetR;
        property Ts[const K: string]: string read GetT write SetT;
      end;
      TV = class(TObject, IV)
        FN: array[0..3] of Integer;
        FD: array[0..3] of Double;
        FS: Single;
        FR: Double;
        FT: string;
        function GetN(I: Integer): Integer;
        procedure SetN(I: Integer; V: Integer);
        function GetD(I: Integer): Double;
        procedure SetD(I: Integer; V: Double);
        function GetS(): Single;
        procedure SetS(V: Single);
        function GetR(): Double;
        procedure SetR(V: Double);
        function GetT(const K: string): string;
        procedure SetT(const K: string; const V: string);
      end;
      THolder = class
        F: IV;
      end;
    function TV.GetN(I: Integer): Integer; begin Result := FN[I]; end;
    procedure TV.SetN(I: Integer; V: Integer); begin FN[I] := V; end;
    function TV.GetD(I: Integer): Double; begin Result := FD[I]; end;
    procedure TV.SetD(I: Integer; V: Double); begin FD[I] := V; end;
    function TV.GetS(): Single; begin Result := FS; end;
    procedure TV.SetS(V: Single); begin FS := V; end;
    function TV.GetR(): Double; begin Result := FR; end;
    procedure TV.SetR(V: Double); begin FR := V; end;
    function TV.GetT(const K: string): string; begin Result := K + '=' + FT; end;
    procedure TV.SetT(const K: string; const V: string); begin FT := K + V; end;
    var X: IV; H: THolder; I: Integer;
    begin
      X := TV.Create();
      X.Ns[1] := 7;
      I := 2;
      X.Ns[I] := X.Ns[1] * 3;
      X.Ds[3] := 2.25;
      X.S := 1.5;
      X.R := X.Ds[3] * 2;
      X.Ts['k'] := 'v';
      WriteLn(X.Ns[1], ' ', X.Ns[I], ' ', X.Ds[3]:0:2, ' ', X.S:0:2, ' ',
        X.R:0:2, ' ', X.Ts['a']);
      H := THolder.Create();
      H.F := X;
      H.F.Ds[0] := H.F.R + 1;
      WriteLn(H.F.Ds[0]:0:2, ' ', H.F.Ns[2], ' ', X.Ds[0]:0:2);
      H.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '7 21 2.25 1.50 4.50 a=kv' + LE +
    '5.50 21 5.50' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_IntfCall_ArgsByDeclaredParams;
const
  Src = '''
    program i1;
    type
      IG = interface
        function Scale(D: Double; N: Integer): Double;
        function Half(S: Single): Single;
        function Many(A, B, C, D, E, F, G, H: Integer; I: Int64; J: Int64): Int64;
        function Floats(A, B, C, D, E, F, G, H, I, J: Double): Double;
        procedure Txt(const S: string; N: Integer);
      end;
      TG = class(TObject, IG)
        function Scale(D: Double; N: Integer): Double;
        function Half(S: Single): Single;
        function Many(A, B, C, D, E, F, G, H: Integer; I: Int64; J: Int64): Int64;
        function Floats(A, B, C, D, E, F, G, H, I, J: Double): Double;
        procedure Txt(const S: string; N: Integer);
      end;
    function TG.Scale(D: Double; N: Integer): Double; begin Result := D * N end;
    function TG.Half(S: Single): Single; begin Result := S / 2 end;
    function TG.Many(A, B, C, D, E, F, G, H: Integer; I: Int64; J: Int64): Int64;
    begin Result := A + B + C + D + E + F + G + H + I * 1000 + J * 100000 end;
    function TG.Floats(A, B, C, D, E, F, G, H, I, J: Double): Double;
    begin Result := A + I * 100 + J * 1000 end;
    procedure TG.Txt(const S: string; N: Integer); begin WriteLn(S, N) end;
    var G: IG; D: Double;
    begin
      G := TG.Create();
      WriteLn(Trunc(G.Scale(2, 4)));
      D := 3.0;
      WriteLn(Trunc(G.Half(D) * 10));
      WriteLn(G.Many(1, 2, 3, 4, 5, 6, 7, 8, 9, 7));
      WriteLn(Trunc(G.Floats(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)));
      G.Txt('n=', 5);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '8' + LE + '15' + LE + '709036' + LE + '10901' + LE +
    'n=5' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_IntfRecordReturn_FloatArgs_AllReceivers;
const
  Src = '''
    program i3;
    type
      TP = record X, Y, Z: Int64; end;
      IG = interface
        function Mk(D: Double; N: Integer): TP;
        function Other: IG;
      end;
      TG = class(TObject, IG)
        function Mk(D: Double; N: Integer): TP;
        function Other: IG;
      end;
      THolder = class
        F: IG;
        procedure Run;
      end;
    function TG.Mk(D: Double; N: Integer): TP; begin Result.X := Trunc(D * 10); Result.Y := N; Result.Z := 3 end;
    function TG.Other: IG; begin Result := Self end;
    procedure THolder.Run;
    var P: TP;
    begin P := F.Mk(2.5, 7); WriteLn(P.X, ' ', P.Y, ' ', P.Z) end;
    var G: IG; P: TP; H: THolder;
    begin
      G := TG.Create();
      P := G.Mk(1.5, 4); WriteLn(P.X, ' ', P.Y, ' ', P.Z);
      P := G.Mk(2, 5); WriteLn(P.X, ' ', P.Y, ' ', P.Z);
      WriteLn(G.Mk(3.5, 6).X);
      P := G.Other().Mk(4.5, 8); WriteLn(P.X, ' ', P.Y);
      H := THolder.Create(); H.F := G; H.Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '15 4 3' + LE + '20 5 3' + LE + '35' + LE + '45 8' + LE +
    '25 7 3' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ProgramGlobals_ReachedOnlyThroughVarArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      IGreet = interface
        function Hi(): string;
      end;
      TGreet = class(IGreet)
        function Hi(): string;
      end;
      TA = class end;
      TB = class(TA) end;
      TAClass = class of TA;
    function TGreet.Hi(): string; begin Result := 'hi' end;
    var
      G: IGreet;
      M: TAClass;
    procedure Fill(var X: IGreet); begin X := TGreet.Create() end;
    procedure Pick(var X: TAClass); begin X := TB end;
    begin
      Fill(G);
      WriteLn(G.Hi());
      Pick(M);
      WriteLn(M = TB)
    end.
    ''', 'hi' + LE + 'True' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceFromGettersAndStaticMembers;
const
  Src = '''
    program f;
    type
      TPt = record X, Y: Integer; end;
      TBig = record A, B, C: Int64; S: string; end;
      TBFn = reference to function(A: Integer): Integer;
      IThing = interface
        function Name(): string;
        function GetNext(): IThing;
        function GetPos(): TPt;
        function GetBig(): TBig;
        function GetFn(): TBFn;
        property Next: IThing read GetNext;
        property Pos: TPt read GetPos;
        property Big: TBig read GetBig;
        property Fn: TBFn read GetFn;
      end;
      TThing = class(TObject, IThing)
        FN: string;
        constructor Create(const N: string);
        function Name(): string;
        function GetNext(): IThing;
        function GetPos(): TPt;
        function GetBig(): TBig;
        function GetFn(): TBFn;
      end;
      TC = class
      public static var
        SI: IThing;
      public
        T: IThing;
        function GetT(): IThing;
        static function GetST(): IThing;
        function GetFn(): TBFn;
        procedure Run();
        property PT: IThing read GetT;
        property PF: TBFn read GetFn;
        static property ST: IThing read GetST;
      end;
    constructor TThing.Create(const N: string); begin FN := N; end;
    function TThing.Name(): string; begin Result := FN; end;
    function TThing.GetNext(): IThing; begin Result := TThing.Create(FN + '+'); end;
    function TThing.GetPos(): TPt; begin Result.X := Length(FN); Result.Y := 5; end;
    function TThing.GetBig(): TBig; begin Result.C := 77; Result.S := FN + '!'; end;
    function TThing.GetFn(): TBFn; begin Result := function(A: Integer): Integer begin Result := A * 3; end; end;
    function TC.GetT(): IThing; begin Result := T; end;
    static function TC.GetST(): IThing; begin Result := TThing.Create('st'); end;
    function TC.GetFn(): TBFn; begin Result := function(A: Integer): Integer begin Result := A + 100; end; end;
    procedure TC.Run();
    var I: IThing;
    begin
      WriteLn('a ', PT.Name());
      WriteLn('b ', Self.PT.Name());
      I := PT;
      WriteLn('c ', I.Name());
      if PT <> nil then WriteLn('d nonnil');
      WriteLn('e ', GetFn()(1));
    end;
    procedure Show(const I: IThing); begin WriteLn('show ', I.Name()); end;
    var C: TC; I, J: IThing; P: TPt; B: TBig; Fv: TBFn;
    begin
      C := TC.Create();
      C.T := TThing.Create('thing');
      C.Run();
      WriteLn('f ', C.PT.Name());
      I := C.PT;
      WriteLn('g ', I.Name());
      Show(C.PT);
      WriteLn('h ', I.Next.Name());
      J := I.Next;
      WriteLn('i ', J.Next.Next.Name());
      Show(I.Next);
      WriteLn('j ', I.Pos.X, ' ', I.Pos.Y);
      P := I.Pos;
      WriteLn('k ', P.X);
      WriteLn('l ', I.Big.S, ' ', I.Big.C);
      B := I.Big;
      WriteLn('m ', B.S);
      Fv := I.Fn;
      WriteLn('o ', Fv(5));
      Fv := C.PF;
      WriteLn('p ', Fv(5));
      TC.SI := TThing.Create('si');
      WriteLn('q ', TC.SI.Name());
      I := TC.SI;
      WriteLn('r ', I.Name());
      WriteLn('s ', TC.ST.Name());
      I := TC.ST;
      WriteLn('t ', I.Name());
      Show(TC.ST);
      Show(TC.SI);
      if I.Next <> nil then WriteLn('u nonnil');
      WriteLn('v ', I.Next.Next.Name(), ' ', TC.ST.Name());
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'a thing' + LineEnding +
    'b thing' + LineEnding +
    'c thing' + LineEnding +
    'd nonnil' + LineEnding +
    'e 101' + LineEnding +
    'f thing' + LineEnding +
    'g thing' + LineEnding +
    'show thing' + LineEnding +
    'h thing+' + LineEnding +
    'i thing+++' + LineEnding +
    'show thing+' + LineEnding +
    'j 5 5' + LineEnding +
    'k 5' + LineEnding +
    'l thing! 77' + LineEnding +
    'm thing!' + LineEnding +
    'o 15' + LineEnding +
    'p 105' + LineEnding +
    'q si' + LineEnding +
    'r si' + LineEnding +
    's st' + LineEnding +
    't st' + LineEnding +
    'show st' + LineEnding +
    'show si' + LineEnding +
    'u nonnil' + LineEnding +
    'v st++ st' + LineEnding, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassCastOfInterfaceCall_ReleasesTheCallRef;
const
  Src = '''
    program P;
    type
      IGreet = interface
        function Hi: Integer;
      end;
      TGreet = class(TObject, IGreet)
        N: Integer;
        S: string;
        function Hi: Integer;
        procedure Bump;
        destructor Destroy; override;
      end;
    function TGreet.Hi: Integer;
    begin
      Result := N;
    end;
    procedure TGreet.Bump;
    begin
      N := N + 1;
    end;
    destructor TGreet.Destroy;
    begin
      WriteLn('gone');
      inherited Destroy();
    end;
    var G: IGreet;
    function MakeI(): IGreet;
    begin
      Result := G;
    end;
    procedure Run;
    begin
      G := TGreet.Create();
      TGreet(MakeI()).N := 5;
      WriteLn(TGreet(MakeI()).N);
      TGreet(MakeI()).S := 'x';
      WriteLn(TGreet(MakeI()).S, TGreet(MakeI()).Hi());
      TGreet(MakeI()).Bump();
      WriteLn(G.Hi());
      G := nil;
      WriteLn('after nil');
    end;
    begin
      Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { every cast use leaked one reference to G's object, so G := nil never
    freed it (BUG-20261009-cast-of-owned-intf-call-leaks): 'gone' must come
    before 'after nil' }
  AssertRunsOnAll(Src,
    '5' + LE + 'x5' + LE + '6' + LE + 'gone' + LE + 'after nil' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_IntfAndMetaclassFieldOfCallResult;
const
  Src = '''
    program P;
    type
      IThing = interface
        function Name(): string;
      end;
      TThing = class(TObject, IThing)
        N: string;
        function Name(): string;
        destructor Destroy(); override;
      end;
      TA = class end;
      TAC = class of TA;
      TObj = class
        FI: IThing;
        FC: TAC;
        destructor Destroy(); override;
      end;
    function TThing.Name(): string;
    begin
      Result := N
    end;
    destructor TThing.Destroy();
    begin
      WriteLn('thing gone');
      inherited Destroy()
    end;
    destructor TObj.Destroy();
    begin
      WriteLn('obj gone');
      inherited Destroy()
    end;
    function MkObj(): TObj;
    var T: TThing;
    begin
      Result := TObj.Create();
      T := TThing.Create();
      T.N := 'tn';
      Result.FI := T;
      Result.FC := TA
    end;
    var
      I: IThing;
      C: TAC;
    begin
      I := MkObj().FI;
      WriteLn(I.Name());
      C := MkObj().FC;
      WriteLn(C = TA);
      WriteLn(MkObj().FI <> nil, MkObj().FC = TA);
      I := nil;
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'obj gone' + LE + 'tn' + LE + 'obj gone' + LE + 'thing gone' + LE +
    'True' + LE + 'TrueTrue' + LE + 'obj gone' + LE + 'thing gone' + LE +
    'obj gone' + LE + 'thing gone' + LE + 'thing gone' + LE + 'end' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ProcFieldCall_AggregateResult;
const
  Src = '''
    program P;
    type
      IThing = interface
        function N(): Integer;
      end;
      TThing = class(TObject, IThing)
        FN: Integer;
        function N(): Integer;
        destructor Destroy(); override;
      end;
      TBig = record A, B, C: Int64; end;
      TIFac = function(): IThing of object;
      TRFac = function(): TBig of object;
      THold = class
        FI: TIFac;
        FR: TRFac;
        FKeep: IThing;
        Count: Integer;
        function MakeI(): IThing;
        function MakeR(): TBig;
        function Again(): IThing;
        procedure Run();
      end;
    function TThing.N(): Integer;
    begin
      Result := FN
    end;
    destructor TThing.Destroy();
    begin
      WriteLn('gone ', FN);
      inherited Destroy()
    end;
    function THold.MakeI(): IThing;
    var T: TThing;
    begin
      Count := Count + 1;
      T := TThing.Create();
      T.FN := Count;
      Result := T
    end;
    function THold.MakeR(): TBig;
    begin
      Result.A := 1;
      Result.B := 2;
      Result.C := 3
    end;
    function THold.Again(): IThing;
    begin
      Result := FI()
    end;
    procedure Show(const I: IThing);
    begin
      WriteLn('show ', I.N())
    end;
    procedure THold.Run();
    var I: IThing; R: TBig; K: Integer;
    begin
      I := FI();
      WriteLn('self local ', I.N());
      FKeep := FI();
      WriteLn('self field ', FKeep.N());
      Show(FI());
      K := FI().N();
      WriteLn('self recv ', K);
      R := FR();
      WriteLn('self rec ', R.A + R.B + R.C, ' ', FR().C)
    end;
    var
      H: THold;
      I: IThing;
      R: TBig;
      K: Integer;
    begin
      H := THold.Create();
      H.FI := @H.MakeI;
      H.FR := @H.MakeR;
      I := H.FI();
      WriteLn('local ', I.N());
      Show(H.FI());
      K := H.FI().N();
      WriteLn('recv ', K);
      I := H.Again();
      WriteLn('result ', I.N());
      R := H.FR();
      WriteLn('rec ', R.A + R.B + R.C, ' ', H.FR().B);
      I := nil;
      H.Run();
      H.FKeep := nil;
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { every transient result is released at its statement's end: each object
    is gone before the next line prints }
  AssertRunsOnAll(Src,
    'local 1' + LE +
    'show 2' + LE + 'gone 2' + LE +
    'gone 3' + LE + 'recv 3' + LE +
    'gone 1' + LE + 'result 4' + LE +
    'rec 6 2' + LE +
    'gone 4' + LE +
    'self local 5' + LE +
    'self field 6' + LE +
    'show 7' + LE + 'gone 7' + LE +
    'gone 8' + LE + 'self recv 8' + LE +
    'self rec 6 3' + LE +
    'gone 5' + LE +
    'gone 6' + LE +
    'end' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ProcFieldCall_AggregateResult_DiscardedAndRepeated;
const
  Src = '''
    program P;
    type
      IThing = interface
        function N(): Integer;
      end;
      TThing = class(TObject, IThing)
        FN: Integer;
        function N(): Integer;
        destructor Destroy(); override;
      end;
      TBig = record A, B, C: Int64; S: string; end;
      TIFac = function(): IThing of object;
      TRFac = function(): TBig of object;
      THold = class
        FI: TIFac;
        FR: TRFac;
        Count: Integer;
        function MakeI(): IThing;
        function MakeR(): TBig;
        procedure Run();
      end;
    function TThing.N(): Integer; begin Result := FN end;
    destructor TThing.Destroy(); begin WriteLn('gone ', FN); inherited Destroy() end;
    function THold.MakeI(): IThing;
    var T: TThing;
    begin Count := Count + 1; T := TThing.Create(); T.FN := Count; Result := T end;
    function THold.MakeR(): TBig;
    begin Result.A := 1; Result.B := 2; Result.C := 3; Result.S := 'x' + IntToStr(Count) end;
    procedure THold.Run();
    var K, Sum: Integer;
    begin
      FI();
      Sum := 0;
      for K := 1 to 3 do Sum := Sum + FI().N();
      WriteLn('self sum ', Sum);
      FR();
      WriteLn(FR().S)
    end;
    var H: THold; K, Sum: Integer; R: TBig;
    begin
      H := THold.Create(); H.FI := @H.MakeI; H.FR := @H.MakeR;
      H.FI();
      Sum := 0;
      for K := 1 to 3 do Sum := Sum + H.FI().N();
      WriteLn('sum ', Sum);
      WriteLn(Assigned(H.FI()));
      H.FR();
      R := H.FR(); WriteLn(R.S, ' ', R.A + R.C);
      H.Run();
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { a discarded result is released, and a call repeated in a loop hands the
    callee a clean result buffer each time (the callee releases what the
    buffer holds when it assigns Result) }
  AssertRunsOnAll(Src,
    'gone 1' + LE + 'gone 2' + LE + 'gone 3' + LE + 'gone 4' + LE +
    'sum 9' + LE + 'True' + LE + 'gone 5' + LE + 'x5 4' + LE +
    'gone 6' + LE + 'gone 7' + LE + 'gone 8' + LE + 'gone 9' + LE +
    'self sum 24' + LE + 'x9' + LE + 'end' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_AsCast_IntoEveryConsumer;
const
  Src = '''
    program P;
    uses sysutils;
    type
      IThing = interface
        function N(): Integer;
      end;
      TThing = class(TObject, IThing)
        FN: Integer;
        function N(): Integer;
        destructor Destroy(); override;
      end;
      TPlain = class end;
      THold = class
        FS: IThing;
        procedure SetFrom(O: TObject);
        function Get(O: TObject): IThing;
      end;
    function TThing.N(): Integer; begin Result := FN end;
    destructor TThing.Destroy(); begin WriteLn('gone ', FN); inherited Destroy() end;
    function Make(AN: Integer): TObject;
    var T: TThing;
    begin T := TThing.Create(); T.FN := AN; Result := T end;
    procedure THold.SetFrom(O: TObject); begin FS := O as IThing end;
    function THold.Get(O: TObject): IThing; begin Result := O as IThing end;
    procedure ByVar(O: TObject; var X: IThing); begin X := O as IThing end;
    procedure ByOut(O: TObject; out X: IThing); begin X := O as IThing end;
    procedure Show(const X: IThing); begin WriteLn('show ', X.N()) end;
    var
      O: TObject; H: THold; I: IThing; A: array of IThing; K: Integer;
    begin
      O := Make(1);
      H := THold.Create();
      H.SetFrom(O); WriteLn('field ', H.FS.N());
      ByVar(O, I); WriteLn('var ', I.N());
      I := nil; ByOut(O, I); WriteLn('out ', I.N());
      I := H.Get(O); WriteLn('result ', I.N());
      SetLength(A, 1); A[0] := O as IThing; WriteLn('elem ', A[0].N());
      Show(O as IThing);
      K := (O as IThing).N(); WriteLn('recv ', K);
      H.FS := Make(2) as IThing; WriteLn('owned ', H.FS.N());
      Show(Make(3) as IThing);
      try
        Show(TPlain.Create() as IThing);
        WriteLn('no raise')
      except
        on E: EInvalidCast do WriteLn('invalid cast')
      end;
      H.FS := nil; I := nil; SetLength(A, 0); O := nil;
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'field 1' + LE + 'var 1' + LE + 'out 1' + LE + 'result 1' + LE +
    'elem 1' + LE + 'show 1' + LE + 'recv 1' + LE + 'owned 2' + LE +
    'show 3' + LE + 'gone 3' + LE + 'invalid cast' + LE +
    'gone 2' + LE + 'gone 1' + LE + 'end' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InPlaceIntfSources_IntoEveryConsumer;
const
  Src = '''
    program Q;
    type
      IThing = interface
        function N(): Integer;
        procedure Take(const X: IThing);
      end;
      TThing = class(TObject, IThing)
        FN: Integer;
        function N(): Integer;
        procedure Take(const X: IThing);
        destructor Destroy(); override;
      end;
      PThing = ^IThing;
      THold = class
        FS: IThing;
        FArr: array[0..1] of IThing;
        function First(): IThing;
        procedure Run(var V: IThing; out W: IThing);
      end;
    var Sum: Integer;
    function TThing.N(): Integer; begin Result := FN end;
    procedure TThing.Take(const X: IThing); begin Sum := Sum + X.N() end;
    destructor TThing.Destroy(); begin WriteLn('gone ', FN); inherited Destroy() end;
    function Mk(AN: Integer): IThing;
    var T: TThing;
    begin T := TThing.Create(); T.FN := AN; Result := T end;
    procedure Take(const X: IThing); begin Sum := Sum + X.N() end;
    procedure Many(A, B, C, D, E: Integer; X, Y, Z: IThing);
    begin Sum := Sum + A + B + C + D + E + X.N() + Y.N() + Z.N() end;
    type TMany = procedure(A, B, C, D, E: Integer; X, Y, Z: IThing);
    function THold.First(): IThing; begin Result := FArr[0] end;
    procedure THold.Run(var V: IThing; out W: IThing);
    var IT: IThing;
    begin
      FS := FArr[1];
      V := FArr[0];
      W := FArr[1];
      IT := FArr[0];
      IT.Take(FArr[1]);
      Take(FArr[0])
    end;
    var
      H: THold; G: array of IThing; P: PThing; A, B, IT, L: IThing; F: TMany;
      T: TThing;
    begin
      H := THold.Create();
      H.FArr[0] := Mk(1); H.FArr[1] := Mk(2);
      SetLength(G, 2); G[0] := Mk(3); P := @G[0];
      L := H.First(); WriteLn('result ', L.N());
      H.Run(A, B); WriteLn('run ', A.N(), ' ', B.N(), ' ', H.FS.N(), ' ', Sum);
      H.FS := G[0]; WriteLn('dyn field ', H.FS.N());
      H.FS := P^; WriteLn('deref field ', H.FS.N());
      G[1] := P^; WriteLn('deref elem ', G[1].N());
      IT := H.FArr[0];
      Sum := 0; IT.Take(G[0]); IT.Take(P^); Take(P^); WriteLn('args ', Sum);
      T := TThing.Create(); T.FN := 4; F := @Many;
      Sum := 0; Many(0, 0, 0, 0, 0, T, H.FArr[1], G[0]); WriteLn('spill ', Sum);
      Sum := 0; F(0, 0, 0, 0, 0, P^, T, G[0]); WriteLn('spill pv ', Sum);
      H.FArr[0] := nil; H.FArr[1] := nil; H.FS := nil;
      A := nil; B := nil; L := nil; IT := nil;
      SetLength(G, 0); T := nil;
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { x86-64 rejected FArr[I] (inside a method) as Result, a field of Self
    and an interface-method argument; a dynamic-array element and P^ in
    several consumers; and passed a class value to a stack-spilled
    interface parameter through a nonexistent '<Name>_itab' symbol }
  AssertRunsOnAll(Src,
    'result 1' + LE + 'run 1 2 2 3' + LE + 'dyn field 3' + LE +
    'deref field 3' + LE + 'deref elem 3' + LE + 'args 9' + LE +
    'spill 9' + LE + 'spill pv 10' + LE +
    'gone 2' + LE + 'gone 1' + LE + 'gone 3' + LE + 'gone 4' + LE +
    'end' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InterfaceCast_IntoEveryConsumer;
const
  Src = '''
    program Q;
    type
      IBase = interface
        function A(): Integer;
      end;
      IDer = interface(IBase)
        function B(): Integer;
      end;
      TImp = class(TObject, IDer)
        FN: Integer;
        function A(): Integer;
        function B(): Integer;
        destructor Destroy(); override;
      end;
      THold = class
        FB: IBase;
        function Get(O: TImp): IBase;
      end;
    function TImp.A(): Integer; begin Result := FN end;
    function TImp.B(): Integer; begin Result := FN * 10 end;
    destructor TImp.Destroy(); begin WriteLn('gone ', FN); inherited Destroy() end;
    function Mk(AN: Integer): TImp; begin Result := TImp.Create(); Result.FN := AN end;
    function THold.Get(O: TImp): IBase; begin Result := IBase(O) end;
    procedure Show(const X: IBase); begin WriteLn('show ', X.A()) end;
    var O: TImp; D: IDer; B: IBase; H: THold; K: Integer;
    begin
      O := Mk(1);
      B := IBase(O); WriteLn('class ', B.A());
      D := O;
      B := IBase(D); WriteLn('upcast ', B.A());
      WriteLn('recv ', IBase(D).A(), ' ', IDer(D).B(), ' ', IBase(O).A());
      Show(IBase(O)); Show(IBase(D));
      H := THold.Create();
      H.FB := IBase(D); WriteLn('field ', H.FB.A());
      B := H.Get(O); WriteLn('result ', B.A());
      Show(IBase(Mk(2)));
      B := IBase(Mk(3)); WriteLn('owned ', B.A());
      K := IBase(Mk(4)).A(); WriteLn('owned recv ', K);
      B := IBase(nil); WriteLn('nil ', Assigned(B));
      H.FB := nil; D := nil; O := nil;
      WriteLn('end')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'class 1' + LE + 'upcast 1' + LE + 'recv 1 10 1' + LE + 'show 1' + LE +
    'show 1' + LE + 'field 1' + LE + 'result 1' + LE + 'show 2' + LE +
    'gone 2' + LE + 'owned 3' + LE + 'gone 4' + LE + 'owned recv 4' + LE +
    'gone 3' + LE + 'nil False' + LE + 'gone 1' + LE + 'end' + LE, 0);
end;

initialization
  RegisterTest(TE2EInterfaceTests);

end.
