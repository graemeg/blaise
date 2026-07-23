{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.classes2;

{ E2E tests for class features: milestone programs, multi-type blocks,
  ToString, InheritsFrom, is/as, inheritance, interfaces, and Supports. }

interface

uses
  blaise.testing, classes, sysutils, cp.test.e2e.base;

type
  [Threaded]
  TE2EClasses2Tests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Phase2Milestone_Stdout;
    procedure TestRun_Phase2Milestone_Valgrind;
    procedure TestRun_Phase3Milestone_Stdout;
    procedure TestRun_Phase3Milestone_Valgrind;
    procedure TestRun_MultiTypeBlock_BothClassesWork;
    procedure TestRun_ForwardClass_CaseDifferentSpelling_RunsClean;
    procedure TestRun_ToString_DefaultReturnsClassName;
    procedure TestRun_ToString_OverrideDispatchedVirtually;
    procedure TestRun_ToString_InheritedOverrideStillReached;
    procedure TestRun_InheritsFrom_SameClass_ReturnsTrue;
    procedure TestRun_InheritsFrom_Parent_ReturnsTrue;
    procedure TestRun_InheritsFrom_GrandParent_ReturnsTrue;
    procedure TestRun_InheritsFrom_Unrelated_ReturnsFalse;
    procedure TestRun_InheritsFrom_Reverse_ReturnsFalse;
    procedure TestRun_InheritsFrom_ClassType_Works;
    procedure TestRun_Is_CorrectSubclass_True;
    procedure TestRun_Is_WrongClass_False;
    procedure TestRun_As_DowncastCallsMethod;
    procedure TestRun_Inherited_CallsParentMethod;
    { inherited call whose Self + args exceed 6 integer registers must spill
      the overflow args to the stack (native arg-register overflow). }
    procedure TestRun_Inherited_ManyArgs_SpillsToStack;
    procedure TestRun_Inherited_VarParam_PassesByReference;
    procedure TestRun_Virtual_OverrideDispatch;
    procedure TestRun_MultiLevel_Inheritance_Chain;
    procedure TestRun_Interface_Dispatch_CallsImpl;
    procedure TestRun_Interface_ARC_NoLeak;
    procedure TestRun_Interface_GlobalNil_LinksAndRuns;
    procedure TestRun_Interface_Is_As_Roundtrip;
    procedure TestRun_Interface_MethodParam_ByValue_Dispatches;
    procedure TestRun_Supports_TwoArg_BooleanResult;
    procedure TestRun_Supports_ThreeArg_AssignsAndCalls;
    procedure TestRun_ConstructorOverload_PicksCorrectArity;
    { A var class parameter aliases the caller's variable: the callee can
      allocate into it (store through the address with ARC) and the caller
      sees the new instance.  Exercises the var-class read (double deref)
      and the ARC store-through-address discipline. }
    procedure TestRun_VarClassParam_CalleeAllocatesForCaller;
    { Regression: native backend passed float args to methods/constructors via
      integer registers instead of the SysV xmm registers — a literal crashed
      codegen, a variable silently used the wrong register. }
    procedure TestRun_MethodFloatArg_Literal_PassedInXmm;
    procedure TestRun_MethodFloatArg_Variable_PassedInXmm;
    procedure TestRun_ConstructorFloatArg_Literal_StoredCorrectly;
    procedure TestRun_ConstructorFloatArg_Variable_StoredCorrectly;
    procedure TestRun_MethodMixedIntFloatString_RegistersInterleave;
    procedure TestRun_MethodMultipleFloats_UseXmm0AndXmm1;
    { >6-register-slot overflow path with float args: the integer args beyond
      the 6 integer registers spill to the stack while floats still take xmm
      registers, so the spill layout must classify by SysV class, not by
      argument position. }
    procedure TestRun_MethodOverflowFloatArgs_Pass;
    procedure TestRun_ConstructorOverflowFloatArgs_Pass;
    procedure TestRun_InheritedOverflowFloatArgs_Pass;
    { Regression: a virtual method called via implicit Self (unqualified
      Foo(), no Self. prefix) must dispatch through the vtable, exactly as
      Self.Foo() does — otherwise it binds the declaring class statically,
      silently breaking polymorphism (and link-failing for an abstract base). }
    procedure TestRun_ImplicitSelfVirtual_DispatchesOverride;
    procedure TestRun_ImplicitSelfAbstractVirtual_LinksAndDispatches;
    procedure TestRun_ImplicitSelfVirtual_NonVirtualStaysStatic;
    procedure TestRun_ImplicitSelfVirtual_IntfReturn_Dispatches;
    procedure TestRun_ImplicitSelfVirtual_RecordReturn_Dispatches;
    procedure TestRun_MethodReadsProgramGlobal;
    procedure TestRun_VarParam_ClassFields_WritebackVisible;
    { Name-resolution priority for unqualified calls inside a class
      method.  Adjacent-level distinctions, top wins:
        1. local vars / parameters
        2. implicit Self.member (incl. inherited via class chain)
        3. program-level / uses-clause unit exports
      Sub-distinctions inside level 2 (own vs parent), and level 3
      (program vs uses-clause), depend on orthogonal mechanisms
      (virtual dispatch; Blaise's duplicate-identifier rule for
      program-level shadowing of unit exports).  They're worth
      pinning separately when their own bugs surface.

      Cross-unit visibility (private skipped, protected accessible to
      subclasses) is a follow-up commit. }
    procedure TestRun_LocalVar_ShadowsOwnMethod;
    procedure TestRun_ParentMethod_ShadowsProgramProc;
    { Explicit qualifiers are unambiguous paths — the priority order
      does not apply.  Self.X must hit a class member; inherited X
      must hit a parent method.  Neither falls through to unit-level. }
    procedure TestRun_ExplicitSelf_AlwaysClassMember;
    procedure TestRun_InheritedCall_AlwaysParent;
    { Regression (issue #64): interface-typed field with same name as a
      program-level global of a different type. }
    procedure TestRun_InterfaceField_ShadowsGlobal_Dispatches;

    { Regression for graemeg/blaise#111: a child class that inherits a
      method-backed property must dispatch the getter/setter to the parent
      that declares them, not to a never-emitted child-mangled symbol. }
    procedure TestRun_InheritedProperty_AccessorsResolveToParent;

    { Class const accessed via the type name (TThing.MaxCount): native
      backend lacked the IsConstant case (codegen error), QBE mis-emitted
      string class consts (invalid IR + phantom _StringRetain). }
    procedure TestRun_ClassConst_IntViaType;
    procedure TestRun_ClassConst_StringViaType;
    procedure TestRun_ClassConst_ViaInstanceAndType;

    { Interface properties: read/write through the interface variable. }
    procedure TestRun_InterfaceProperty_ReadWrite;
    { Accessor names with non-declared casing must still link (symbols are
      case-sensitive; Pascal resolution is not), and program-level classes
      implementing interfaces must link when units are in the uses chain
      (program-scope symbols carry no unit prefix). }
    procedure TestRun_InterfaceProperty_CaseMismatchAndUses;

    { Statement-position method call through a non-Self interface field:
      H.S.Note(); — expression position already worked. }
    procedure TestRun_InterfaceFieldCall_StatementPosition;

    { var-param class: field reads/writes must double-deref (slot -> caller
      var -> instance); single-deref corrupted the caller frame. }
    procedure TestRun_VarParamClass_FieldReadWrite;
    { Nested proc with captured vars AND regular params: signature emission. }
    procedure TestRun_NestedProc_CaptureAndParams;
    { var Double param (pointer arrives in an int register, not xmm) and
      captured float read/write through the _cap_ slot. }
    procedure TestRun_VarParamFloat_CapturedFloat;
    { var-param dynamic array: element writes and SetLength must reach the
      caller's array (slot -> caller var -> data pointer). }
    procedure TestRun_VarParamDynArray_WriteAndGrow;
    { var-param static array element write and var-param PChar byte write. }
    procedure TestRun_VarParamStaticArray_PChar;
    { var-param interface: method dispatch and reassignment through the
      var param must reach the caller's variable. }
    procedure TestRun_VarParamInterface_DispatchAndReassign;

    { Metaclass-var constructor dispatch: cls.Create() runs the most-derived
      ctor body via vtable (implicitly virtual), not the base ctor statically. }
    procedure TestRun_MetaclassCreate_DispatchesToDerived;
    { Metaclass-var ctor with args: cls.Create(N) passes args correctly. }
    procedure TestRun_MetaclassCreate_WithArgs;
    { Metaclass-var ctor in statement position (result discarded): allocates,
      dispatches the most-derived ctor, then frees the instance. }
    procedure TestRun_MetaclassCreate_StatementDiscardsResult;
    { Direct TFoo.Create stays static (no vtable dispatch). }
    procedure TestRun_DirectCreate_StaysStatic;
    { ClassCreate builtin still works (backwards compat) and now dispatches
      the ctor body via vtable too. }
    procedure TestRun_ClassCreate_StillWorks;
    { Forward class declaration with a managed (string) field: the forward
      stub must complete into the same type so the full class — including its
      ARC field — compiles and runs correctly. }
    procedure TestRun_ForwardClass_MutualRefRuns;

    { Implicit Int64/Integer→float conversion when the assignment target is a
      class FIELD (both Self.Field and bare implicit-Self forms), for Double
      and Single fields.  Regression: QBE deposited the raw integer bits into
      the float slot; native stored a Double into a Single slot (movss of a
      double) without narrowing. }
    procedure TestRun_IntToFloatField_Converts;
    procedure TestRun_SelfIndexedRecordFieldAssign;
    { BUG-037: an unqualified call to a method must not be shadowed by a
      same-named PROGRAM-LEVEL variable (case-insensitive: global LOG vs
      method Log).  Locals/params still shadow methods. }
    procedure TestRun_UnqualifiedMethodCall_GlobalVarSameName;
    procedure TestRun_UnqualifiedFuncCall_GlobalVarSameName;
    { Inc/Dec on an explicit field RECEIVER: Inc(H.FCount) on a class instance,
      Inc(R.RI[1]) / Inc(R.RD[1],5) on static/dyn array fields.  The native
      EmitIncDec branch hand-rolled the slot address and dropped both
      IsClassAccess handling (wrote beside the receiver's pointer slot) and the
      IsArrayAccess subscript (BUG-20260723-native-incdec-field-receiver). }
    procedure TestRun_IncDec_FieldReceiver;
    { In-place l-value ops AND reads on an implicit-Self CLASS-typed field
      (FInner.Count, FInner.Dyn[0]) inside a method.  QBE's EmitLValueAddr and
      field-read arms tested IsClassAccess/whole-field before IsImplicitSelf,
      so it either emitted a load of a nonexistent %_var_<field> (l-value) or
      dropped the array subscript and returned the data pointer (read)
      (BUG-20260723-qbe-lvalue-implicitself-classfield). }
    procedure TestRun_ImplicitSelf_ClassField_LValueAndRead;
    { Address-of a subscripted array field of an implicit-Self class field:
      P := @FInner.Arr[1] / @FInner.Dyn[1] inside a method.  QBE's
      EmitAddrOfExpr tested IsClassAccess before IsImplicitSelf, loading a
      nonexistent %_var_<field> (BUG-20260723-qbe-addrof-implicitself-classfield-elem). }
    procedure TestRun_AddrOf_ImplicitSelf_ClassFieldElem;
  end;

implementation

procedure TE2EClasses2Tests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-classes2');
end;

const
  LE = #10;

  SrcMultiTypeBlock =
    '''
        program Prg;
        type
          TCounter = class
            FN: Integer;
            procedure Inc;
            begin Self.FN := Self.FN + 1 end;
            property Value: Integer read FN;
          end;
        var N: Integer;
        type
          TDoubler = class
            function Double(X: Integer): Integer;
            begin Result := X * 2 end;
          end;
        var
          C: TCounter;
          D: TDoubler;
        begin
          C := TCounter.Create();
          D := TDoubler.Create();
          C.Inc(); C.Inc(); C.Inc();
          N := D.Double(C.Value);
          WriteLn(N)
        end.
        ''';

  { Forward-declared TNode referenced by TEdge before its full definition,
    then completed with a managed (string) field and a back-reference. }
  SrcForwardClass =
    '''
        program Prg;
        type
          TNode = class;
          TEdge = class
            Target: TNode;
          end;
          TNode = class
            Name: string;
            Link: TEdge;
          end;
        var
          N: TNode;
          E: TEdge;
        begin
          N := TNode.Create();
          N.Name := 'hello';
          E := TEdge.Create();
          E.Target := N;
          N.Link := E;
          WriteLn(E.Target.Name);
          N.Free();
          E.Free()
        end.
        ''';

  SrcToStringDefault = '''
    program Prg;
    type
      TFoo = class end;
      TBar = class(TFoo) end;
    var F: TFoo; B: TBar;
    begin
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
    end.
    ''';

  SrcToStringOverride = '''
    program Prg;
    type
      TFoo = class
        function ToString: string; override;
      end;
      TBar = class(TFoo)
        function ToString: string; override;
      end;
      function TFoo.ToString: string;
      begin Result := 'foo!' end;
      function TBar.ToString: string;
      begin Result := 'bar!' end;
    var F: TFoo; B: TFoo;
    begin
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
    end.
    ''';

  SrcToStringInheritedOverride = '''
    program Prg;
    type
      TFoo = class
        function ToString: string; override;
      end;
      TBar = class(TFoo) end;
      function TFoo.ToString: string;
      begin Result := 'foo override' end;
    var F: TFoo; B: TFoo;
    begin
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
    end.
    ''';

  SrcInheritsFromBase =
    '''
        program Prg;
        type TBase = class end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
        end.
        ''';

  SrcInheritsFromParent =
    '''
        program Prg;
        type TBase = class end;
             TChild = class(TBase) end;
        var C: TChild;
        begin
          C := TChild.Create();
          if C.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free();
        end.
        ''';

  SrcInheritsFromGrandParent =
    '''
        program Prg;
        type TBase = class end;
             TChild = class(TBase) end;
             TGrandChild = class(TChild) end;
        var G: TGrandChild;
        begin
          G := TGrandChild.Create();
          if G.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          G.Free();
        end.
        ''';

  SrcInheritsFromUnrelated =
    '''
        program Prg;
        type TBase = class end;
             TUnrelated = class end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TUnrelated) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
        end.
        ''';

  SrcInheritsFromReverse =
    '''
        program Prg;
        type TBase = class end;
             TChild = class(TBase) end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TChild) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
        end.
        ''';

  SrcInheritsFromClassType =
    '''
        program Prg;
        type TBase = class end;
             TChild = class(TBase) end;
        var C: TChild;
            CT: Pointer;
        begin
          C := TChild.Create();
          CT := C.ClassType;
          if CT.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free();
        end.
        ''';

  SrcIsTrue = '''
    program Prg;
    type
      TAnimal = class end;
      TDog = class(TAnimal) end;
    var D: TAnimal;
    begin
      D := TDog.Create();
      if D is TDog then WriteLn('yes');
      D.Free()
    end.
    ''';

  SrcIsFalse = '''
    program Prg;
    type
      TAnimal = class end;
      TDog = class(TAnimal) end;
      TCat = class(TAnimal) end;
    var D: TAnimal;
    begin
      D := TDog.Create();
      if D is TCat then WriteLn('yes') else WriteLn('no');
      D.Free()
    end.
    ''';

  SrcAsDowncast = '''
    program Prg;
    type
      TBase = class
        function Name: string; virtual;
      end;
      TChild = class(TBase)
        FVal: Integer;
        function Name: string; override;
      end;
    function TBase.Name: string;
    begin Result := 'base' end;
    function TChild.Name: string;
    begin Result := 'child' end;
    var B: TBase;
    begin
      B := TChild.Create();
      WriteLn((B as TChild).Name());
      B.Free()
    end.
    ''';

  SrcInherited = '''
    program Prg;
    type
      TBase = class
        function Val: Integer; virtual;
      end;
      TChild = class(TBase)
        function Val: Integer; override;
      end;
    function TBase.Val: Integer;
    begin Result := 10 end;
    function TChild.Val: Integer;
    var B: Integer;
    begin
      inherited Val();
      B := Result;
      Result := B + 5
    end;
    var C: TChild;
    begin
      C := TChild.Create();
      WriteLn(C.Val());
      C.Free()
    end.
    ''';

  { Regression: an `inherited Method(args)` call whose Self + args occupy more
    than the 6 integer argument registers.  The native inherited-call sequence
    only handled the all-in-registers case (it popped every slot into a
    register, walking past the 6 available), so an inherited call with 6+ args
    aborted codegen ("arg register index 6 out of range").  Here Self + 7 ints
    = 8 register slots, forcing the overflow to spill to the stack.  TBase.Sum
    = 1+..+7 = 28; TChild.Sum doubles it via inherited => 56. }
  SrcInheritedManyArgs = '''
    program Prg;
    type
      TBase = class
        function Sum(a, b, c, d, e, f, g: Integer): Integer; virtual;
      end;
      TChild = class(TBase)
        function Sum(a, b, c, d, e, f, g: Integer): Integer; override;
      end;
    function TBase.Sum(a, b, c, d, e, f, g: Integer): Integer;
    begin Result := a + b + c + d + e + f + g end;
    function TChild.Sum(a, b, c, d, e, f, g: Integer): Integer;
    begin Result := inherited Sum(a, b, c, d, e, f, g) * 2 end;
    var o: TChild;
    begin
      o := TChild.Create();
      WriteLn(o.Sum(1, 2, 3, 4, 5, 6, 7));
      o.Free()
    end.
    ''';

  { Regression: `inherited Foo(X)` where the parent method has a var/out param.
    The inherited-call arg loop had no var-param branch, so it passed the
    loaded VALUE (a `w`) where the callee expects an address (`l`) — the parent
    then dereferenced a small integer as a pointer and the program crashed. }
  SrcInheritedVarParam = '''
    program Prg;
    type
      TBase = class
        procedure Bump(var X: Integer); virtual;
      end;
      TDer = class(TBase)
        procedure Bump(var X: Integer); override;
      end;
    procedure TBase.Bump(var X: Integer);
    begin X := X + 10 end;
    procedure TDer.Bump(var X: Integer);
    begin
      inherited Bump(X);
      X := X + 1
    end;
    var
      D: TDer;
      N: Integer;
    begin
      D := TDer.Create();
      N := 5;
      D.Bump(N);
      WriteLn(N);
      D.Free()
    end.
    ''';

  SrcVirtualOverride = '''
    program Prg;
    type
      TShape = class
        function Area: Integer; virtual;
      end;
      TSquare = class(TShape)
        FSide: Integer;
        function Area: Integer; override;
      end;
    function TShape.Area: Integer;
    begin Result := 0 end;
    function TSquare.Area: Integer;
    begin Result := FSide * FSide end;
    var S: TShape;
    begin
      S := TSquare.Create();
      TSquare(S).FSide := 4;
      WriteLn(S.Area());
      S.Free()
    end.
    ''';

  SrcMultiLevelChain = '''
    program Prg;
    type
      TA = class
        function Lvl: Integer; virtual;
      end;
      TB = class(TA)
        function Lvl: Integer; override;
      end;
      TC = class(TB)
        function Lvl: Integer; override;
      end;
    function TA.Lvl: Integer; begin Result := 1 end;
    function TB.Lvl: Integer; begin Result := 2 end;
    function TC.Lvl: Integer; begin Result := 3 end;
    var A: TA;
    begin
      A := TC.Create();
      WriteLn(A.Lvl());
      A.Free()
    end.
    ''';

  SrcIntfDispatch = '''
    program Prg;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var G: IGreeter;
        H: THello;
    begin
      H := THello.Create();
      G := H;
      G.Greet();
      H.Free()
    end.
    ''';

  { Regression: assigning nil to an interface-typed GLOBAL variable.  An
    interface global is emitted as a fat-pointer pair ($G_obj / $G_itab); the
    `:= nil` path previously fell through to a scalar store against a bare $G
    symbol with no data definition, causing an undefined-reference link error.
    Must be an e2e test: the IR-only harness never links, so it cannot see it. }
  SrcIntfGlobalNil = '''
    program Prg;
    type
      ISpeaker = interface
        procedure Speak;
      end;
      TSpeaker = class(TObject, ISpeaker)
        procedure Speak;
      end;
    procedure TSpeaker.Speak;
    begin WriteLn('spoke') end;
    var G: ISpeaker;
    begin
      G := TSpeaker.Create();
      G.Speak();
      G := nil;
      WriteLn('after nil')
    end.
    ''';

  SrcIntfIsAs = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TPrinter = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TPrinter.Print;
    begin WriteLn('printing') end;
    var
      Obj: TObject;
      P: IPrinter;
    begin
      Obj := TPrinter.Create();
      if Obj is IPrinter then
      begin
        P := Obj as IPrinter;
        P.Print()
      end;
      Obj.Free()
    end.
    ''';

  { Regression: a class METHOD taking a by-value interface parameter.  The
    method-codegen path emitted the param as a single `w` slot instead of the
    two-slot fat pointer the standalone-routine path uses, so QBE rejected the
    `storel %_par_X` ("invalid type for first operand") and the program failed
    to compile.  The method must receive obj+itab and dispatch through them. }
  SrcIntfMethodParam = '''
    program Prg;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      THello = class(TObject, IGreeter)
        function Greet: Integer;
      end;
      TUser = class
        function Use(G: IGreeter): Integer;
      end;
    function THello.Greet: Integer;
    begin Result := 42 end;
    function TUser.Use(G: IGreeter): Integer;
    begin Result := G.Greet() + 1 end;
    var
      H: THello;
      I: IGreeter;
      U: TUser;
    begin
      H := THello.Create();
      I := H;
      U := TUser.Create();
      WriteLn(U.Use(I))
    end.
    ''';

  { Regression (issue #64): class has an interface-typed field 'im' AND the
    program declares a same-named global variable 'im' of the class type.
    Inside the constructor and a method, bare 'im' must resolve to the field
    (Iprinter), not the global (Tmi).  Previously the semantic analyser found
    the global first and reported a type-mismatch. }
  SrcIntfFieldShadowsGlobal = '''
    program Prg;
    type
      Iprinter = interface
        procedure print;
      end;
      Toutput = class(TObject, Iprinter)
        procedure print;
      end;
      Tmi = class
        im: Iprinter;
        constructor create(am: Iprinter);
        procedure use;
      end;
    procedure Toutput.print;
    begin
      WriteLn('printed');
    end;
    constructor Tmi.Create(am: Iprinter);
    begin
      im := am;
    end;
    procedure Tmi.use;
    begin
      im.print();
    end;
    var
      im: Tmi;
    begin
      im := Tmi.Create(Toutput.Create());
      im.use();
    end.
    ''';

  SrcSupportsTwoArgRun = '''
    program Prg;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var Obj: TObject;
    begin
      Obj := THello.Create();
      if Supports(Obj, IGreeter) then
        WriteLn('yes')
      else
        WriteLn('no');
      Obj.Free()
    end.
    ''';

  SrcSupportsThreeArgRun = '''
    program Prg;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var Obj: TObject;
        G: IGreeter;
    begin
      Obj := THello.Create();
      if Supports(Obj, IGreeter, G) then
        G.Greet()
      else
        WriteLn('no');
      Obj.Free()
    end.
    ''';

  { Constructor overload where the 2-arg variant is declared first.  The
    1-arg call site must resolve to the 1-arg constructor; otherwise the
    semantic pass rejects the program with "No default value for parameter
    'B' of 'Create'".  Picks the body via A only, so the output proves
    the 1-arg constructor body actually ran. }
  { Regression for issue #43: a class method body must be able to read and
    write a program-level global variable declared above the class type. }
  SrcMethodReadsProgramGlobal =
    '''
        program GlobalAccessBug;
        var
          gValue: Integer;
        type
          TFoo = class
            function GetValue: Integer;
          end;
        function TFoo.GetValue: Integer;
        begin
          Result := gValue
        end;
        var
          Foo: TFoo;
        begin
          gValue := 42;
          Foo := TFoo.Create();
          WriteLn(Foo.GetValue());
          Foo.Free()
        end.
        ''';

  SrcVarParamClassFields =
    '''
        program VarParamClassFields;
        procedure Fill(var V: Int64; var F: Boolean);
        begin
          V := 4096;
          F := True
        end;
        type
          TNode = class
            Value: Int64;
            IsBig: Boolean;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          Fill(N.Value, N.IsBig);
          WriteLn(N.Value);
          WriteLn(N.IsBig);
          N.Free()
        end.
        ''';

  { ----- Name-resolution priority (Option A: single-program tests).
    Visibility (private / protected across units) is a follow-up. ----- }

  { Level 1 beats level 2: a local procedural-typed variable shadows a
    class method of the same name.  This is the use case in
    blaise.testing.TTestCase.RunTest (`var Run: TRunMethod`). }
  SrcResolve_LocalVar_OverOwnMethod =
    '''
        program ResLocalVar;
        function Helper: Integer;
        begin Result := 42 end;
        type
          TFn  = function: Integer;
          TFoo = class
            function Compute: Integer;
            function Run: Integer;
          end;
        function TFoo.Compute: Integer;
        begin Result := 100 end;
        function TFoo.Run: Integer;
        var Compute: TFn;
        begin
          Compute := @Helper;
          Result  := Compute()
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          WriteLn(F.Run());
          F.Free()
        end.
        ''';

  { Level 2 beats level 3: a class method shadows a program-level
    proc.  A subclass with no own method X but with an inherited X
    (and a program-level proc X also in scope) — the unqualified call
    inside the subclass binds to the inherited method, not the
    program-level proc.  Pre-fix, the global lookup ran first and
    bound to the program-level Tag (output '1'); post-fix the
    implicit-Self check finds parent.Tag and wins (output '2'). }
  SrcResolve_ParentMethod_OverProgramProc =
    '''
        program ResParentOverProgram;
        function Tag: Integer;
        begin Result := 1 end;
        type
          TParent = class
            function Tag: Integer;
            function Echo: Integer;
          end;
          TChild = class(TParent)
          end;
        function TParent.Tag: Integer;
        begin Result := 2 end;
        function TParent.Echo: Integer;
        begin Result := Tag() end;
        var C: TChild;
        begin
          C := TChild.Create();
          WriteLn(C.Echo());
          C.Free()
        end.
        ''';

  { `inherited X;` is an explicit qualifier that calls the parent's X
    statically — does NOT go through subclass override, does NOT fall
    through to any program-level X.  Statement form is used because
    Blaise doesn't yet parse `inherited X` in expression context;
    parent's body sets Result, which Child.FromInh returns. }
  SrcResolve_InheritedAlwaysParent =
    '''
        program ResInherited;
        type
          TParent = class
            function Tag: Integer;
          end;
          TChild = class(TParent)
            function Tag: Integer;
            function FromInh: Integer;
          end;
        function TParent.Tag: Integer;
        begin Result := 1 end;
        function TChild.Tag: Integer;
        begin Result := 2 end;
        function TChild.FromInh: Integer;
        begin
          inherited Tag()
        end;
        var C: TChild;
        begin
          C := TChild.Create();
          WriteLn(C.FromInh());
          C.Free()
        end.
        ''';

  { Self.X is an explicit path: it MUST resolve to a member of Self's
    class hierarchy, regardless of any same-named local var that
    would otherwise win in the unqualified priority order. }
  SrcResolve_ExplicitSelf_AlwaysClassMember =
    '''
        program ResExplicitSelf;
        type
          TFoo = class
            function Compute: Integer;
            function Run: Integer;
          end;
        function TFoo.Compute: Integer;
        begin Result := 200 end;
        function TFoo.Run: Integer;
        var Compute: Integer;
        begin
          Compute := 7;
          Result  := Self.Compute()
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          WriteLn(F.Run());
          F.Free()
        end.
        ''';


  SrcCtorOverloadArity =
    '''
        program Prg;
        type
          TFoo = class
            FA: Integer;
            constructor Create(A: Integer; B: Integer); overload;
            constructor Create(A: Integer); overload;
          end;
          constructor TFoo.Create(A: Integer; B: Integer);
          begin Self.FA := A + B end;
          constructor TFoo.Create(A: Integer);
          begin Self.FA := A end;
        var F: TFoo;
        begin
          F := TFoo.Create(42);
          WriteLn(F.FA);
          F.Free()
        end.
        ''';

function LoadMilestoneFile(const APath: string; out ASrc: string): Boolean;
var Lst: TStringList;
begin
  Result := False;
  if not FileExists(APath) then Exit;
  Lst := TStringList.Create();
  try
    Lst.LoadFromFile(APath);
    ASrc := Lst.Text;
    Result := True;
  finally
    Lst.Free();
  end;
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode: Integer;
  Expected: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
  // Walk up to project root looking for tests/phase2_milestone.pas
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase2_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase2_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase2_milestone.pas not found');
    Exit;
  end;
  AssertTrue('compile+run milestone', CompileAndRun(Src, Output, RCode));
  AssertEquals('milestone exit code', 0, RCode);
  Expected :=
    'count=4' + LE +
    '--- walk ---' + LE +
    '  value=40' + LE +
    '  tag=0' + LE +
    '  marked=False' + LE +
    '  value=30' + LE +
    '  tag=1' + LE +
    '  marked=True' + LE +
    '  value=20' + LE +
    '  tag=0' + LE +
    '  marked=False' + LE +
    '  value=10' + LE +
    '  tag=0' + LE +
    '  marked=False' + LE +
    'pop=40' + LE +
    'pop=30' + LE +
    'count_after_pops=2' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase2_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase2_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase2_milestone.pas not found');
    Exit;
  end;
  { real ARC-leak guard (valgrind is blind to the mmap allocator) — runs
    regardless of valgrind availability }
  AssertLeakFreeOnAll(Src, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EClasses2Tests.TestRun_Phase3Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode: Integer;
  Expected: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase3_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase3_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase3_milestone.pas not found');
    Exit;
  end;
  AssertTrue('compile+run milestone', CompileAndRun(Src, Output, RCode));
  AssertEquals('milestone exit code', 0, RCode);
  Expected :=
    'list.count=5' + LE +
    'list[0]=10' + LE +
    'list[4]=50' + LE +
    'count_after_delete=4' + LE +
    'list[1]_after_delete=30' + LE +
    'dict.count=4' + LE +
    'beta=2' + LE +
    'has_gamma=True' + LE +
    'beta_after_update=99' + LE +
    'count_after_remove=3' + LE +
    'has_alpha_after_remove=False' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase3Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase3_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase3_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase3_milestone.pas not found');
    Exit;
  end;
  { real ARC-leak guard (valgrind is blind to the mmap allocator) — runs
    regardless of valgrind availability }
  AssertLeakFreeOnAll(Src, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('phase3 milestone has leaks or errors:' + LE + Log);
  end;
end;

procedure TE2EClasses2Tests.TestRun_MultiTypeBlock_BothClassesWork;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiTypeBlock, Output, RCode));
  AssertEquals('TCounter(3).Double = 6', '6', Trim(Output));
end;

procedure TE2EClasses2Tests.TestRun_ForwardClass_CaseDifferentSpelling_RunsClean;
begin
  { Regression for issue #162: a forward class declaration whose completing
    full declaration differs only in case must link and run.  Before the fix
    the program aborted at load time with
    `undefined symbol: _FieldCleanup_TState`. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
        program P;
        type
          TState = class;
          Tstate = class
            FName: string;
          end;
        var S: Tstate;
        begin
          S := Tstate.Create();
          S.FName := 'hello';
          WriteLn(S.FName);
          S.Free()
        end.
        ''',
    'hello' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ToString_DefaultReturnsClassName;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcToStringDefault, 'TFoo' + LE + 'TBar' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ToString_OverrideDispatchedVirtually;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('override reached through static base type',
    'foo!' + LE + 'bar!' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ToString_InheritedOverrideStillReached;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringInheritedOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited override still reached',
    'foo override' + LE + 'foo override' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_SameClass_ReturnsTrue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromBase, 'yes' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Parent_ReturnsTrue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromParent, 'yes' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_GrandParent_ReturnsTrue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromGrandParent, 'yes' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Unrelated_ReturnsFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromUnrelated, 'no' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Reverse_ReturnsFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromReverse, 'no' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_ClassType_Works;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritsFromClassType, 'yes' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_Is_CorrectSubclass_True;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsTrue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Is_WrongClass_False;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsFalse, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('no', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_As_DowncastCallsMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcAsDowncast, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child', 'child' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_CallsParentMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInherited, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('15', '15' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_ManyArgs_SpillsToStack;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedManyArgs, '56' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_VarParam_PassesByReference;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritedVarParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('5+10+1', '16' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Virtual_OverrideDispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVirtualOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('16', '16' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_MultiLevel_Inheritance_Chain;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiLevelChain, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3', '3' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Dispatch_CallsImpl;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_ARC_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
end;

procedure TE2EClasses2Tests.TestRun_Interface_GlobalNil_LinksAndRuns;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfGlobalNil, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('spoke then after nil',
    'spoke' + LE + 'after nil' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Is_As_Roundtrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfIsAs, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('printing', 'printing' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_MethodParam_ByValue_Dispatches;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfMethodParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('greet+1', '43' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_TwoArg_BooleanResult;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsTwoArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_ThreeArg_AssignsAndCalls;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsThreeArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorOverload_PicksCorrectArity;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcCtorOverloadArity, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1-arg constructor body ran', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_VarClassParam_CalleeAllocatesForCaller;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TThing = class
      public
        V: Integer;
      end;
    procedure EnsureThing(var T: TThing);
    begin
      if T = nil then
        T := TThing.Create();
      T.V := 7
    end;
    var X: TThing;
    begin
      X := nil;
      EnsureThing(X);
      WriteLn(X.V);
      X.Free()
    end.
    ''',
    '7' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodFloatArg_Literal_PassedInXmm;
begin
  AssertRunsOnAll(
    '''
    program c;
    type TX = class procedure Take(d: Double); end;
    procedure TX.Take(d: Double); begin WriteLn(d); end;
    var x: TX;
    begin x := TX.Create(); x.Take(1.5); end.
    ''',
    '1.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodFloatArg_Variable_PassedInXmm;
begin
  AssertRunsOnAll(
    '''
    program f;
    type TX = class procedure Take(d: Double); end;
    procedure TX.Take(d: Double); begin WriteLn(d); end;
    var x: TX; y: Double;
    begin x := TX.Create(); y := 1.5; x.Take(y); end.
    ''',
    '1.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorFloatArg_Literal_StoredCorrectly;
begin
  AssertRunsOnAll(
    '''
    program ctl;
    type TN = class V: Double; constructor CreateFloat(d: Double); end;
    constructor TN.CreateFloat(d: Double); begin V := d; end;
    var n: TN;
    begin n := TN.CreateFloat(2.5); WriteLn(n.V); end.
    ''',
    '2.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorFloatArg_Variable_StoredCorrectly;
begin
  AssertRunsOnAll(
    '''
    program ct;
    type TN = class V: Double; constructor CreateFloat(d: Double); end;
    constructor TN.CreateFloat(d: Double); begin V := d; end;
    var n: TN; y: Double;
    begin y := 2.5; n := TN.CreateFloat(y); WriteLn(n.V); end.
    ''',
    '2.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodMixedIntFloatString_RegistersInterleave;
begin
  { Exercises int + float + string interleaving: the string and Int64 take
    integer arg registers, the Double takes an xmm register, independently. }
  AssertRunsOnAll(
    '''
    program mix;
    type TX = class procedure M(const s: string; i: Int64; d: Double); end;
    procedure TX.M(const s: string; i: Int64; d: Double);
    begin WriteLn('s=', s, ' i=', i, ' d=', d); end;
    var x: TX;
    begin x := TX.Create(); x.M('hi', 7, 3.5); end.
    ''',
    's=hi i=7 d=3.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodMultipleFloats_UseXmm0AndXmm1;
begin
  { Two Double/Single args must land in distinct xmm registers (xmm0, xmm1),
    interleaved with an integer arg that consumes an integer register. }
  AssertRunsOnAll(
    '''
    program mf;
    type TX = class procedure M(a: Double; i: Int64; b: Double; c: Single); end;
    procedure TX.M(a: Double; i: Int64; b: Double; c: Single);
    begin WriteLn('a=', a, ' i=', i, ' b=', b, ' c=', c); end;
    var x: TX;
    begin x := TX.Create(); x.M(1.5, 9, 2.5, 3.5); end.
    ''',
    'a=1.5 i=9 b=2.5 c=3.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodOverflowFloatArgs_Pass;
begin
  { 9 args (5 int register, 2 float xmm, 1 int spilled to stack) plus Self:
    exercises the >6-slot overflow path with floats. i6 is the 6th integer arg
    and must reach %r9, not the stack, since the two floats consumed xmm not
    integer registers. }
  AssertRunsOnAll(
    '''
    program ovm;
    type TX = class
      procedure M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    end;
    procedure TX.M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    begin WriteLn(i1,' ',i2,' ',i3,' ',i4,' ',i5,' ',d1,' ',d2,' ',i6); end;
    var x: TX;
    begin x := TX.Create(); x.M(1,2,3,4,5, 6.5, 7.5, 8); end.
    ''',
    '1 2 3 4 5 6.5 7.5 8' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorOverflowFloatArgs_Pass;
begin
  AssertRunsOnAll(
    '''
    program ovc;
    type TN = class
      R: Double;
      constructor Create(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    end;
    constructor TN.Create(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    begin R := d1 + d2 + i6; end;
    var n: TN;
    begin n := TN.Create(1,2,3,4,5, 6.5, 7.5, 8); WriteLn(n.R); end.
    ''',
    '22' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_InheritedOverflowFloatArgs_Pass;
begin
  AssertRunsOnAll(
    '''
    program ovi;
    type
      TBase = class
        procedure M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64); virtual;
      end;
      TDer = class(TBase)
        procedure M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64); override;
      end;
    procedure TBase.M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    begin WriteLn('base ',i1,' ',d1,' ',d2,' ',i6); end;
    procedure TDer.M(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6: Int64);
    begin inherited M(i1,i2,i3,i4,i5,d1,d2,i6); WriteLn('der ',d1,' ',d2); end;
    var x: TDer;
    begin x := TDer.Create(); x.M(1,2,3,4,5, 6.5, 7.5, 9); end.
    ''',
    'base 1 6.5 7.5 9' + LE + 'der 6.5 7.5' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelfVirtual_DispatchesOverride;
begin
  { TBase.Run calls Emit() unqualified; Self is a TLeaf, so the override must
    run.  A static bind would print BASE. }
  AssertRunsOnAll(
    '''
    program a;
    type
      TBase = class
        procedure Emit; virtual;
        procedure Run;
      end;
      TLeaf = class(TBase)
        procedure Emit; override;
      end;
    procedure TBase.Emit; begin WriteLn('BASE'); end;
    procedure TBase.Run;  begin Emit(); end;
    procedure TLeaf.Emit; begin WriteLn('LEAF'); end;
    var b: TBase;
    begin b := TLeaf.Create(); b.Run(); end.
    ''',
    'LEAF' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelfAbstractVirtual_LinksAndDispatches;
begin
  { Abstract base method has no body; an unqualified Emit(x) must vtable-
    dispatch (else: undefined symbol TBase_Emit at link). }
  AssertRunsOnAll(
    '''
    program a;
    type
      TArg  = class end;
      TBase = class
      protected
        procedure Emit(A: TArg); virtual; abstract;
      public
        procedure Run;
      end;
      TLeaf = class(TBase)
      protected
        procedure Emit(A: TArg); override;
      end;
    procedure TBase.Run; var x: TArg; begin x := TArg.Create(); Emit(x); end;
    procedure TLeaf.Emit(A: TArg); begin WriteLn('leaf'); end;
    var b: TBase;
    begin b := TLeaf.Create(); b.Run(); end.
    ''',
    'leaf' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelfVirtual_NonVirtualStaysStatic;
begin
  { An unqualified call to a NON-virtual method must still resolve (a static
    direct call); this guards against over-eager vtable dispatch. }
  AssertRunsOnAll(
    '''
    program a;
    type TX = class
      procedure Helper;
      procedure Run;
    end;
    procedure TX.Helper; begin WriteLn('helper'); end;
    procedure TX.Run; begin Helper(); end;
    var x: TX;
    begin x := TX.Create(); x.Run(); end.
    ''',
    'helper' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelfVirtual_IntfReturn_Dispatches;
begin
  { Implicit-Self virtual method returning an interface (sret) must dispatch
    to the override. }
  AssertRunsOnAll(
    '''
    program a;
    type
      IFoo = interface
        function Name: String;
      end;
      TFoo = class(TObject, IFoo)
        function Name: String;
      end;
      TBase = class
        function MakeFoo: IFoo; virtual;
        function Run: String;
      end;
      TLeaf = class(TBase)
        function MakeFoo: IFoo; override;
      end;
    function TFoo.Name: String; begin Result := 'foo'; end;
    function TBase.MakeFoo: IFoo; begin Result := nil; end;
    function TBase.Run: String;
    var f: IFoo;
    begin f := MakeFoo(); if f = nil then Result := 'nil' else Result := f.Name(); end;
    function TLeaf.MakeFoo: IFoo; begin Result := TFoo.Create(); end;
    var b: TBase;
    begin b := TLeaf.Create(); WriteLn(b.Run()); end.
    ''',
    'foo' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelfVirtual_RecordReturn_Dispatches;
begin
  { Implicit-Self virtual method returning a record (sret) must dispatch to
    the override. }
  AssertRunsOnAll(
    '''
    program a;
    type
      TPt = record X: Int64; end;
      TBase = class
        function Make: TPt; virtual;
        function Run: Int64;
      end;
      TLeaf = class(TBase)
        function Make: TPt; override;
      end;
    function TBase.Make: TPt; begin Result.X := 100; end;
    function TBase.Run: Int64; var p: TPt; begin p := Make(); Result := p.X; end;
    function TLeaf.Make: TPt; begin Result.X := 200; end;
    var b: TBase;
    begin b := TLeaf.Create(); WriteLn(b.Run()); end.
    ''',
    '200' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MethodReadsProgramGlobal;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMethodReadsProgramGlobal, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('global read by method', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_VarParam_ClassFields_WritebackVisible;
var Output: string; RCode: Integer;
begin
  { Regression for bugs.txt BUG-001 — Fill(N.Value, N.IsBig) where N is a
    class reference must address into the heap object, not into the storage
    slot of N itself.  Before the fix the writes landed in unrelated memory
    and the WriteLn calls printed 0 / False. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamClassFields, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('var-param writeback visible through class field', '4096' + LE + 'True' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_LocalVar_ShadowsOwnMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_LocalVar_OverOwnMethod, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('local var wins over class method', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ParentMethod_ShadowsProgramProc;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_ParentMethod_OverProgramProc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited method wins over program-level proc', '2' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ExplicitSelf_AlwaysClassMember;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_ExplicitSelf_AlwaysClassMember, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Self.X reaches class method despite local var X', '200' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritedCall_AlwaysParent;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_InheritedAlwaysParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited Tag reaches parent despite subclass override', '1' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InterfaceField_ShadowsGlobal_Dispatches;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfFieldShadowsGlobal, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('interface dispatch through field shadowing global', 'printed' + LE, Output);
end;

const
  SrcInterfaceProperty = '''
    program Prg;
    type
      IInter = interface
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        property Value: Integer read GetValue write SetValue;
      end;
      IChild = interface(IInter)
        procedure Bump();
      end;
      TFace = class(TObject, IInter, IChild)
        FVal: Integer;
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        procedure Bump();
        property Value: Integer read GetValue write SetValue;
      end;
    function TFace.GetValue(): Integer;
    begin
      Result := FVal;
    end;
    procedure TFace.SetValue(AValue: Integer);
    begin
      FVal := AValue;
    end;
    procedure TFace.Bump();
    begin
      FVal := FVal + 1;
    end;
    var
      C: TFace;
      I: IInter;
      K: IChild;
    begin
      C := TFace.Create();
      C.Value := 13;
      writeln(C.Value);
      I := TFace.Create();
      I.Value := 21;
      writeln(I.Value);
      I.Value := I.Value + 1;
      writeln(I.Value);
      K := TFace.Create();
      K.Value := 40;
      K.Bump();
      writeln(K.Value);
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_InterfaceProperty_ReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInterfaceProperty,
    '13' + LE + '21' + LE + '22' + LE + '41' + LE, 0);
end;

const
  { graemeg/blaise#111 — Tchild inherits classValue (a method-backed
    property) from Tbase; the read and write must reach Tbase's accessors. }
  SrcInheritedProperty = '''
    program Prg;
    type
      Tbase = class
      private
        fValue: Integer;
      public
        procedure setValue(AValue: Integer);
        function getValue: Integer;
        property classValue: Integer read getValue write setValue;
      end;
      Tchild = class(Tbase)
        procedure childAct;
      end;
    procedure Tbase.setValue(AValue: Integer);
    begin fValue := AValue end;
    function Tbase.getValue: Integer;
    begin Result := fValue end;
    procedure Tchild.childAct;
    begin writeln('act') end;
    var child: Tchild;
    begin
      child := Tchild.Create();
      child.classValue := 12;
      writeln(child.classValue);
      child.Free()
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_InheritedProperty_AccessorsResolveToParent;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedProperty, '12' + LE, 0);
end;

const
  SrcClassConstInt = '''
    program Prg;
    type TThing = class const MaxCount = 10; end;
    begin WriteLn(TThing.MaxCount) end.
    ''';

  SrcClassConstStr = '''
    program Prg;
    type TThing = class const Tag = 'hi'; end;
    var s: string;
    begin
      s := TThing.Tag + '!';
      WriteLn(s);
      WriteLn(TThing.Tag)
    end.
    ''';

  SrcClassConstInstAndType = '''
    program Prg;
    type
      TThing = class
        const MaxCount = 10;
        function Limit: Integer; begin Result := MaxCount end;
      end;
    var t: TThing;
    begin
      t := TThing.Create;
      WriteLn(t.Limit());
      WriteLn(TThing.MaxCount);
      t := nil
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_ClassConst_IntViaType;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassConstInt, '10' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ClassConst_StringViaType;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassConstStr, 'hi!' + LE + 'hi' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ClassConst_ViaInstanceAndType;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassConstInstAndType, '10' + LE + '10' + LE, 0);
end;

const
  SrcIntfPropCaseUses = '''
    program Prg;
    uses classes;
    type
      Iinter = interface
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        property prop: Integer read getValue write setValue;
      end;
      Tface = class(TObject, Iinter)
        fProp: Integer;
        function GetValue(): Integer;
        procedure SetValue(AValue: Integer);
        property prop: Integer read getValue write setValue;
      end;
    function Tface.GetValue(): Integer;
    begin
      Result := fProp;
    end;
    procedure Tface.SetValue(AValue: Integer);
    begin
      fProp := AValue;
    end;
    var
      ift: Tface;
      iit: Iinter;
    begin
      ift := Tface.Create();
      ift.prop := 13;
      writeln(ift.prop);
      iit := Tface.Create();
      iit.prop := 29;
      writeln(iit.prop);
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_InterfaceProperty_CaseMismatchAndUses;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcIntfPropCaseUses, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('output (qbe)', '13' + LE + '29' + LE, Output);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcIntfPropCaseUses, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('output (native)', '13' + LE + '29' + LE, Output);
end;

const
  SrcIntfFieldCallStmt = '''
    program Prg;
    type
      IShape = interface
        procedure Note();
        function Area(K: Integer): Integer;
      end;
      TSq = class(TObject, IShape)
        procedure Note();
        function Area(K: Integer): Integer;
      end;
      THolder = class
        S: IShape;
      end;
    procedure TSq.Note();
    begin
      writeln('note');
    end;
    function TSq.Area(K: Integer): Integer;
    begin
      Result := K * K;
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := TSq.Create();
      writeln(H.S.Area(3));
      H.S.Note();
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_InterfaceFieldCall_StatementPosition;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldCallStmt, '9' + LE + 'note' + LE, 0);
end;

const
  SrcVarParamClass = '''
    program Prg;
    type
      TBox = class
        V: Integer;
        W: Integer;
      end;
    procedure MutB(var B: TBox);
    begin
      B.V := B.V + 98;
      B.W := B.V * 2;
      writeln(B.V);
    end;
    procedure Swap(var B: TBox);
    var T: TBox;
    begin
      T := TBox.Create();
      T.V := 500;
      B := T;
    end;
    var
      Box: TBox;
    begin
      Box := TBox.Create();
      Box.V := 1;
      MutB(Box);
      writeln(Box.V);
      writeln(Box.W);
      Swap(Box);
      writeln(Box.V);
    end.
    ''';

  SrcNestedCaptureParams = '''
    program Prg;
    procedure Outer();
    var
      Total: Integer;
      Name: string;
      procedure Inner(K: Integer; Tag: string);
      begin
        Total := Total + K;
        Name := Name + Tag;
      end;
    begin
      Total := 5;
      Name := 'x';
      Inner(7, 'y');
      Inner(8, 'z');
      writeln(Total);
      writeln(Name);
    end;
    begin
      Outer();
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_VarParamClass_FieldReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamClass,
    '99' + LE + '99' + LE + '198' + LE + '500' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_NestedProc_CaptureAndParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedCaptureParams, '20' + LE + 'xyz' + LE, 0);
end;

const
  SrcVarParamFloat = '''
    program Prg;
    procedure SetD(var D: Double);
    begin
      D := 2.5;
    end;
    procedure Outer();
    var
      X: Double;
      procedure Bump(F: Double);
      begin
        X := X + F;
      end;
    begin
      X := 1.0;
      SetD(X);
      writeln(X);
      Bump(0.5);
      Bump(1.0);
      writeln(X);
    end;
    begin
      Outer();
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_VarParamFloat_CapturedFloat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamFloat, '2.5' + LE + '4' + LE, 0);
end;

const
  SrcVarParamDynArr = '''
    program Prg;
    type
      TIntArr = array of Integer;
    procedure MutArr(var A: TIntArr);
    begin
      writeln(A[1]);
      A[2] := 99;
    end;
    procedure GrowArr(var A: TIntArr);
    begin
      SetLength(A, 6);
      A[5] := 55;
    end;
    var
      Arr: TIntArr;
      I: Integer;
    begin
      SetLength(Arr, 4);
      for I := 0 to 3 do
        Arr[I] := I * 10;
      MutArr(Arr);
      writeln(Arr[2]);
      GrowArr(Arr);
      writeln(Length(Arr), ' ', Arr[5]);
    end.
    ''';

  SrcVarParamSAPChar = '''
    program Prg;
    type
      TFive = array[0..4] of Integer;
    procedure MutSA(var A: TFive);
    begin
      writeln(A[1]);
      A[2] := 77;
    end;
    procedure MutPC(var P: PChar);
    begin
      P[0] := Chr(88);
    end;
    var
      SA: TFive;
      Buf: string;
      PC: PChar;
      I: Integer;
    begin
      for I := 0 to 4 do
        SA[I] := I * 10;
      MutSA(SA);
      writeln(SA[2]);
      Buf := Chr(97) + Chr(98) + Chr(99);
      PC := PChar(Buf);
      MutPC(PC);
      writeln(Buf);
    end.
    ''';

  SrcVarParamIntf = '''
    program Prg;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        FCount: Integer;
        procedure Greet;
        begin
          FCount := FCount + 1;
          writeln('hello ', FCount);
        end;
      end;
    procedure UseIntf(var G: IGreeter);
    begin
      G.Greet();
    end;
    procedure Swap(var G: IGreeter; H2: THello);
    begin
      G := H2;
    end;
    var
      H, HB: THello;
      G: IGreeter;
    begin
      H := THello.Create();
      HB := THello.Create();
      HB.FCount := 100;
      G := H;
      UseIntf(G);
      UseIntf(G);
      writeln(H.FCount);
      Swap(G, HB);
      UseIntf(G);
      writeln(HB.FCount);
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_VarParamDynArray_WriteAndGrow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamDynArr,
    '10' + LE + '99' + LE + '6 55' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_VarParamStaticArray_PChar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamSAPChar,
    '10' + LE + '77' + LE + 'Xbc' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_VarParamInterface_DispatchAndReassign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamIntf,
    'hello 1' + LE + 'hello 2' + LE + '2' + LE + 'hello 101' + LE + '101' + LE, 0);
end;

{ ---------- Metaclass-var constructor dispatch tests ---------- }

const SrcMetaclassCreateDerived = '''
    program Prg;
    type
      TAnimal = class(TObject)
        constructor Create;
      end;
      TDog = class(TAnimal)
        constructor Create;
      end;
      TAnimalClass = class of TAnimal;
    constructor TAnimal.Create;
    begin WriteLn('animal') end;
    constructor TDog.Create;
    begin WriteLn('dog') end;
    procedure MakeAndGreet(C: TAnimalClass);
    var A: TAnimal;
    begin
      A := C.Create();
      A.Free()
    end;
    begin
      MakeAndGreet(TAnimal);
      MakeAndGreet(TDog)
    end.
    ''';

const SrcMetaclassCreateArgs = '''
    program Prg;
    type
      TBase = class(TObject)
        FVal: Integer;
        constructor Create(N: Integer);
      end;
      TChild = class(TBase)
        constructor Create(N: Integer);
      end;
      TBaseClass = class of TBase;
    constructor TBase.Create(N: Integer);
    begin FVal := N end;
    constructor TChild.Create(N: Integer);
    begin FVal := N * 10 end;
    procedure Run(C: TBaseClass; N: Integer);
    var B: TBase;
    begin
      B := C.Create(N);
      WriteLn(B.FVal);
      B.Free()
    end;
    begin
      Run(TBase, 3);
      Run(TChild, 3)
    end.
    ''';

{ Metaclass-var constructor in STATEMENT position (result discarded):
  cls.Create(); must allocate, run the most-derived ctor for its side
  effects, then free the unreachable instance — not crash. Regression:
  the statement-call lowering used to treat the metaclass typeinfo pointer
  as the object and call a garbage vtable slot.  Destroy bumps gFreed, so
  the trailing '1' proves the discarded instance was freed, not leaked. }
const SrcMetaclassCreateStatement = '''
    program Prg;
    type
      TBase = class(TObject)
        constructor Create(N: Integer); virtual;
        destructor Destroy; override;
      end;
      TChild = class(TBase)
        constructor Create(N: Integer); override;
      end;
      TBaseClass = class of TBase;
    var gVal: Integer;
    var gFreed: Integer;
    constructor TBase.Create(N: Integer);
    begin gVal := N end;
    destructor TBase.Destroy;
    begin gFreed := gFreed + 1; inherited Destroy() end;
    constructor TChild.Create(N: Integer);
    begin inherited Create(N); gVal := gVal * 10 end;
    procedure Run(C: TBaseClass; N: Integer);
    begin
      C.Create(N)
    end;
    begin
      Run(TBase, 4);   WriteLn(gVal);
      Run(TChild, 4);  WriteLn(gVal);
      WriteLn(gFreed)
    end.
    ''';

const SrcDirectCreateStatic = '''
    program Prg;
    type
      TBase = class(TObject)
        constructor Create;
      end;
      TChild = class(TBase)
        constructor Create;
      end;
    constructor TBase.Create;
    begin WriteLn('base') end;
    constructor TChild.Create;
    begin WriteLn('child') end;
    begin
      TBase.Create().Free();
      TChild.Create().Free()
    end.
    ''';

const SrcClassCreateStillWorks = '''
    program Prg;
    type
      TFoo = class(TObject)
        constructor Create;
      end;
      TBar = class(TFoo)
        constructor Create;
      end;
      TFooClass = class of TFoo;
    constructor TFoo.Create;
    begin WriteLn('foo') end;
    constructor TBar.Create;
    begin WriteLn('bar') end;
    var C: TFooClass;
    begin
      C := TBar;
      ClassCreate(C).Free();
      ClassCreate(TFoo).Free()
    end.
    ''';

procedure TE2EClasses2Tests.TestRun_MetaclassCreate_DispatchesToDerived;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMetaclassCreateDerived,
    'animal' + LE + 'dog' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MetaclassCreate_WithArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMetaclassCreateArgs,
    '3' + LE + '30' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_MetaclassCreate_StatementDiscardsResult;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMetaclassCreateStatement,
    '4' + LE + '40' + LE + '2' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_DirectCreate_StaysStatic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDirectCreateStatic,
    'base' + LE + 'child' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ClassCreate_StillWorks;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassCreateStillWorks,
    'bar' + LE + 'foo' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_SelfIndexedRecordFieldAssign;
const
  Src =
    'program test_self_idx_rec;' + LE +
    'type' + LE +
    '  TFrame = record' + LE +
    '    Count: Integer;' + LE +
    '  end;' + LE +
    '  TThing = class' + LE +
    '    FStack: array of TFrame;' + LE +
    '    procedure Go;' + LE +
    '  end;' + LE +
    'procedure TThing.Go;' + LE +
    'begin' + LE +
    '  SetLength(Self.FStack, 1);' + LE +
    '  Self.FStack[0].Count := Self.FStack[0].Count + 1;' + LE +
    '  WriteLn(Self.FStack[0].Count)' + LE +
    'end;' + LE +
    'var t: TThing;' + LE +
    'begin' + LE +
    '  t := TThing.Create();' + LE +
    '  t.Go()' + LE +
    'end.';
  SrcDirect =
    'program test_self_idx_direct;' + LE +
    'type' + LE +
    '  TThing = class' + LE +
    '    FItems: array of Integer;' + LE +
    '    procedure Go;' + LE +
    '  end;' + LE +
    'procedure TThing.Go;' + LE +
    'begin' + LE +
    '  SetLength(Self.FItems, 2);' + LE +
    '  Self.FItems[0] := 42;' + LE +
    '  Self.FItems[1] := 99;' + LE +
    '  WriteLn(Self.FItems[0]);' + LE +
    '  WriteLn(Self.FItems[1])' + LE +
    'end;' + LE +
    'var t: TThing;' + LE +
    'begin' + LE +
    '  t := TThing.Create();' + LE +
    '  t.Go()' + LE +
    'end.';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDirect, '42' + LE + '99' + LE, 0);
  AssertRunsOnAll(Src, '1' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ForwardClass_MutualRefRuns;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForwardClass, Output, RCode));
  AssertEquals('forward-declared TNode field read back', 'hello', Trim(Output));
end;

const
  SrcIntToFloatField =
    '''
        program Prg;
        type
          TFoo = class
            FD: Double;
            FS: Single;
            procedure SetD(AValue: Int64);
            begin Self.FD := AValue end;     { Int64 -> Double, Self.Field }
            procedure SetDBare(AValue: Int64);
            begin FD := AValue end;          { Int64 -> Double, implicit Self }
            procedure SetS(AValue: Integer);
            begin Self.FS := AValue end;     { Integer -> Single, Self.Field }
            procedure SetSBare(AValue: Integer);
            begin FS := AValue end;          { Integer -> Single, implicit Self }
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.SetD(7);
          WriteLn(Format('%g', [F.FD]));
          F.SetDBare(42);
          WriteLn(Format('%g', [F.FD]));
          F.SetS(5);
          WriteLn(Format('%g', [F.FS]));
          F.SetSBare(9);
          WriteLn(Format('%g', [F.FS]))
        end.
        ''';

procedure TE2EClasses2Tests.TestRun_IntToFloatField_Converts;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { All four forms convert the integer to the field's float width — including
    Integer->Single, where the native backend had stored a Double into the
    4-byte Single slot. }
  AssertTrue('compile+run', CompileAndRun(SrcIntToFloatField, Output, RCode));
  AssertEquals('Int64/Integer→float field stores convert',
    '7' + LE + '42' + LE + '5' + LE + '9', Trim(Output));
end;

procedure TE2EClasses2Tests.TestRun_UnqualifiedMethodCall_GlobalVarSameName;
const
  Src = '''
    program p;
    type
      TLogger = class
      public
        procedure Log(AMsg: string);
        procedure Info(AMsg: string);
      end;
    procedure TLogger.Log(AMsg: string);
    begin
      WriteLn(AMsg)
    end;
    procedure TLogger.Info(AMsg: string);
    begin
      Log(AMsg)   { must bind to TLogger.Log, not the global LOG }
    end;
    var
      LOG: TLogger;
    begin
      LOG := TLogger.Create();
      LOG.Info('hi')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hi' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_UnqualifiedFuncCall_GlobalVarSameName;
const
  { expression position: the value-returning twin of the statement case }
  Src = '''
    program p;
    type
      TCalc = class
      public
        function Total(A: Integer): Integer;
        function Twice(A: Integer): Integer;
      end;
    function TCalc.Total(A: Integer): Integer;
    begin
      Result := A + 1
    end;
    function TCalc.Twice(A: Integer): Integer;
    begin
      Result := Total(A) * 2   { must bind to TCalc.Total, not global TOTAL }
    end;
    var
      TOTAL: Integer;
      C: TCalc;
    begin
      TOTAL := 99;
      C := TCalc.Create();
      WriteLn(C.Twice(5))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_IncDec_FieldReceiver;
const
  Src = '''
    program P;
    type
      THold = class
      public
        FCount: Integer;
        FArr: array[0..2] of Integer;
        FDyn: array of Integer;
      end;
      TRec = record
        RI: array[0..2] of Integer;
        RD: array of Integer;
      end;
    var
      H: THold;
      R: TRec;
    begin
      H := THold.Create();
      H.FCount := 40;
      Inc(H.FCount);
      Dec(H.FCount, 1);
      Inc(H.FCount, 5);
      H.FArr[0] := 7; H.FArr[1] := 40; Inc(H.FArr[1]);
      SetLength(H.FDyn, 3);
      H.FDyn[1] := 100; Inc(H.FDyn[1], 7);
      R.RI[0] := 3; R.RI[1] := 40; Inc(R.RI[1]);
      SetLength(R.RD, 3);
      R.RD[1] := 200; Inc(R.RD[1], 5);
      WriteLn(H.FCount, ' ', H.FArr[0], ' ', H.FArr[1], ' ', H.FDyn[1]);
      WriteLn(R.RI[0], ' ', R.RI[1], ' ', R.RD[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A dropped subscript / missing IsClassAccess wrote the wrong slot: FArr[0]
    and RI[0] must be UNTOUCHED, the [1] elements incremented, and FCount must
    reach 45 without corrupting the receiver's own slot. }
  AssertRunsOnAll(Src, '45 7 41 107' + LE + '3 41 205' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_ImplicitSelf_ClassField_LValueAndRead;
const
  Src = '''
    program P;
    type
      TInner = class
      public
        Count: Integer;
        S: string;
        Arr: array[0..2] of Integer;
        Dyn: array of Integer;
      end;
      TOuter = class
      public
        FInner: TInner;
        procedure Go;
      end;
    procedure AddOne(var X: Integer);
    begin X := X + 1 end;
    procedure TOuter.Go;
    begin
      FInner := TInner.Create();
      FInner.Count := 10;
      Inc(FInner.Count);            { implicit-Self class field as Inc l-value }
      AddOne(FInner.Count);         { same shape as a var argument }
      FInner.S := 'hi';
      FInner.Arr[1] := 42;
      SetLength(FInner.Dyn, 2);     { SetLength on implicit-Self class field }
      FInner.Dyn[0] := 7;
      FInner.Dyn[1] := 9;
      WriteLn(FInner.Count, ' ', FInner.S[1], ' ', FInner.Arr[1]);
      WriteLn(FInner.Dyn[0], ' ', FInner.Dyn[1])
    end;
    var O: TOuter;
    begin
      O := TOuter.Create();
      O.Go()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Count=12 (Inc+AddOne), S[1]='i'=105, Arr[1]=42, Dyn[0]=7 Dyn[1]=9.
    Both the l-value side (Inc/AddOne/SetLength) and the read side (subscripted
    Dyn/Arr, char S[1]) must be correct on both backends. }
  AssertRunsOnAll(Src, '12 105 42' + LE + '7 9' + LE, 0);
end;

procedure TE2EClasses2Tests.TestRun_AddrOf_ImplicitSelf_ClassFieldElem;
const
  Src = '''
    program P;
    type
      PInt = ^Integer;
      TInner = class
      public
        Arr: array[0..3] of Integer;
        Dyn: array of Integer;
      end;
      TOuter = class
      public
        FInner: TInner;
        procedure Go;
      end;
    procedure TOuter.Go;
    var P: PInt;
    begin
      FInner := TInner.Create();
      FInner.Arr[1] := 42;
      SetLength(FInner.Dyn, 2);
      FInner.Dyn[1] := 77;
      P := @FInner.Arr[1];
      WriteLn(P^);
      P := @FInner.Dyn[1];
      WriteLn(P^)
    end;
    var O: TOuter;
    begin
      O := TOuter.Create();
      O.Go()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { @FInner.Arr[1] and @FInner.Dyn[1] must resolve through Self, not a
    nonexistent %_var_FInner. }
  AssertRunsOnAll(Src, '42' + LE + '77' + LE, 0);
end;

initialization
  RegisterTest(TE2EClasses2Tests);

end.
