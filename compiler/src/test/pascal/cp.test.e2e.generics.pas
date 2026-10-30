{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.generics;

{ End-to-end tests for generics — compile + run on BOTH backends
  (AssertRunsOnAll), so the generated code is actually exercised rather than
  only the IR substring.  Grew out of the test-hardening sweep; each test
  pins behaviour that the IR/semantic-only generics tests cannot see. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EGenericsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { array-of-T fields of a generic class and record hold managed and plain
      elements }
    procedure TestRun_ArrayOfTypeParamFields;
    { BUG-20261022-generic-type-method-overloads: overloaded methods,
      constructors and virtual methods of generic classes and records, the
      generic declared in a unit; one virtual overload is overridden, and
      TBox<Integer> holds two overloads substitution made identical }
    procedure TestRun_GenericTypeOverloads;
    procedure TestRun_TwoInstances_SelfCallReachesOwnInstance;
    procedure TestRun_GenericForIn_UserEnumerator;
    procedure TestRun_IMap_OneCallSiteBothImplementations;
    procedure TestRun_TOrderedDictionary_KeepsInsertionOrder;
    procedure TestRun_TDictionary_AddLookupUpdateRemove;
    procedure TestRun_TDictionary_DynArrayValue;
    procedure TestRun_TSet_IncludeExcludeContains;
    procedure TestRun_StackQueueList_OrderAcrossGrow;
    { Generic free functions }
    procedure TestRun_GenericFunc_IntAndString;
    procedure TestRun_GenericFunc_TypedLocal;
    procedure TestRun_GenericFunc_ParamlessTypedLocalReturn;
    procedure TestRun_GenericFunc_TwoTypedLocals;
    { Generic classes / records }
    procedure TestRun_GenericClass_GetSet;
    procedure TestRun_GenericRecord_Fields;
    procedure TestRun_GenericClass_MethodTypedLocal;
    { Multiple type params + distinct instantiations }
    procedure TestRun_GenericRecord_TwoTypeParams;
    procedure TestRun_GenericClass_DistinctInstantiations;
    { Nesting }
    procedure TestRun_NestedGeneric_TBoxOfTBox;
    { Generic base names are case-insensitive (GH #212) }
    procedure TestRun_GenericRef_MixedCaseSpellings_OneType;
    { Local variable named after the type parameter (var t: T) — must not be
      rejected as shadowing a visible type. }
    procedure TestRun_GenericClass_LocalNamedLikeTypeParam;
    procedure TestRun_GenericRecord_LocalNamedLikeTypeParam;
    { Non-generic class inheriting from a generic-class instance
      (class(TBox<Integer>)) — parent classification + symbol mangling. }
    procedure TestRun_InheritFromGenericInstance_MethodAndField;
    procedure TestRun_InheritFromGenericInstance_VirtualOverride;
    { Generic class implementing a (non-generic) interface, used through the
      interface — class(IVal) on a generic template must wire AddImplements. }
    procedure TestRun_GenericClassImplementsInterface;
    procedure TestRun_GenericClassImplementsInterface_MethodArgs;
    { Generic METHODS (method-level <T>): a method declaring its own type
      parameter, instantiated per call site (obj.M<Integer>(...)). }
    procedure TestRun_GenericMethod_Pick;
    procedure TestRun_GenericMethod_TwoInstantiations;
    procedure TestRun_GenericMethod_UsesSelfField;
    procedure TestRun_GenericMethod_TwoTypeParams;
    procedure TestRun_GenericMethod_OutOfLineImpl;

    { Open-array parameters whose ELEMENT type is the class's type parameter
      (BUG-20260803-generic-open-array-elem-type) }
    procedure TestRun_GenericOpenArray_ElementTypeIsT;
    procedure TestRun_GenericOpenArray_PassesElementToTMethod;
    procedure TestRun_GenericOpenArray_StaticFactory;
    procedure TestRun_GenericOpenArray_TwoInstantiations;

    { Member visibility survives import of a generic }
    procedure TestRun_GenericImport_PrivateMethodIsRejected;
    procedure TestRun_GenericImport_PublicMethodStillReachable;
    { GH #228: TDictionary with numeric keys and values, and with a static
      array as the value type (x86-64 failed to assemble the instance:
      its symbols carried the '[0..3]' of the array type) }
    procedure TestRun_Dictionary_NumericAndStaticArrayTypeArgs;
    { a generic function instance called more than once ("Ambiguous
      overload" on the second call) }
    procedure TestRun_GenericFunc_CalledTwice;
    { GH #217: generic procedures and a discarded generic function called as
      statements -- one and two type parameters, var parameters, after
      `if` -- (it was "Bare reference to 'GenericProc' requires ()") }
    procedure TestRun_GenericProcedure_CalledAsStatement;
    { The type parameter is in scope in a generic function's body: a
      generic class constructed over T (TBox<T>.Create()) and SizeOf(T)
      (they failed with "Unknown type '^T' for field in 'TList<T>'" and
      "Undeclared identifier 'T'") }
    procedure TestRun_GenericFunc_BodyUsesTypeParam;
    { T(X), a value cast to the type parameter, at every integer kind and an
      enum, with boundary values, in a generic class method and a generic
      function -- the result matches the concrete cast.  arm64 failed to
      compile it (BUG-20261028-arm64-typeparam-cast). }
    procedure TestRun_TypeParamCast_EveryIntegerKind;
  end;

implementation

const
  LE = #10;

procedure TE2EGenericsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-generics');
end;

const
  SrcFuncIntStr = '''
    program Prg;
    function Max<T>(A, B: T): T; begin if A > B then Result := A else Result := B end;
    function Pick<T>(C: Boolean; A, B: T): T; begin if C then Result := A else Result := B end;
    begin
      WriteLn(Max<Integer>(3, 7));
      WriteLn(Pick<string>(True, 'yes', 'no'))
    end.
    ''';

  SrcFuncTypedLocal = '''
    program Prg;
    function Echo<T>(X: T): T; var tmp: T; begin tmp := X; Result := tmp end;
    begin WriteLn(Echo<Integer>(8)) end.
    ''';

  SrcFuncParamlessLocal = '''
    program Prg;
    function Zero<T>: T; var v: T; begin Result := v end;
    begin WriteLn(Zero<Integer>()) end.
    ''';

  SrcFuncTwoLocals = '''
    program Prg;
    function Sum<T>(A, B: T): T; var x, y: T; begin x := A; y := B; Result := x + y end;
    begin WriteLn(Sum<Integer>(20, 22)) end.
    ''';

  SrcClassGetSet = '''
    program Prg;
    type TBox<T> = class
      FV: T;
      procedure SetV(V: T); begin FV := V end;
      function GetV: T; begin Result := FV end;
    end;
    var b: TBox<Integer>;
    begin b := TBox<Integer>.Create(); b.SetV(99); WriteLn(b.GetV()); b.Free() end.
    ''';

  SrcRecordFields = '''
    program Prg;
    type TPair<T> = record A, B: T; end;
    var pr: TPair<Integer>;
    begin pr.A := 10; pr.B := 32; WriteLn(pr.A + pr.B) end.
    ''';

  SrcClassMethodLocal = '''
    program Prg;
    type TBox<T> = class
      FV: T;
      function Get: T; var tmp: T; begin tmp := FV; Result := tmp end;
      procedure Put(X: T); var local: T; begin local := X; FV := local end;
    end;
    var b: TBox<Integer>;
    begin b := TBox<Integer>.Create(); b.Put(33); WriteLn(b.Get()); b.Free() end.
    ''';

  SrcRecordTwoParams = '''
    program Prg;
    type TKV<K, V> = record Key: K; Val: V; end;
    var kv: TKV<string, Integer>;
    begin kv.Key := 'age'; kv.Val := 40; WriteLn(kv.Key, '=', kv.Val) end.
    ''';

  SrcDistinctInst = '''
    program Prg;
    type TBox<T> = class FV: T; procedure SetV(V: T); begin FV := V end; function GetV: T; begin Result := FV end; end;
    var bi: TBox<Integer>; bs: TBox<string>;
    begin
      bi := TBox<Integer>.Create(); bi.SetV(5);
      bs := TBox<string>.Create(); bs.SetV('hi');
      WriteLn(bi.GetV(), ' ', bs.GetV());
      bi.Free(); bs.Free()
    end.
    ''';

  SrcNestedBox = '''
    program Prg;
    type TBox<T> = class
      FV: T;
      procedure SetV(V: T); begin FV := V end;
      function GetV: T; begin Result := FV end;
    end;
    var outer: TBox<TBox<Integer>>; inner: TBox<Integer>;
    begin
      inner := TBox<Integer>.Create(); inner.SetV(7);
      outer := TBox<TBox<Integer>>.Create(); outer.SetV(inner);
      WriteLn(outer.GetV().GetV());
      outer.Free(); inner.Free()
    end.
    ''';

{ GH #212.  A generic referenced under a differently-cased spelling must
  resolve to the SAME instantiation, not fail and not mint a second one.

  The IR-level tests assert that the template resolves and that the instances
  are identical descriptors; this one proves the program actually links and
  runs — one monomorphisation means one set of emitted methods, and the
  assignment `c := a` below only compiles if all three spellings really are the
  same type.

  The odd spelling comes FIRST deliberately: the defect was order-dependent,
  and a leading exact-case reference masked it. }
const
  SrcMixedCaseGeneric =
    '''
    program p;
    type
      TBox<T> = class
        FValue: T;
        procedure SetV(AV: T);
        function GetV(): T;
      end;
      TIntBox = tbox<Integer>;
    procedure TBox<T>.SetV(AV: T);
    begin
      Self.FValue := AV
    end;
    function TBox<T>.GetV(): T;
    begin
      Result := Self.FValue
    end;
    var
      a: tbox<Integer>;
      b: TBOX<Integer>;
      c: TIntBox;
    begin
      a := tbox<Integer>.Create();
      a.SetV(11);
      WriteLn(a.GetV());
      b := TBOX<Integer>.Create();
      b.SetV(22);
      WriteLn(b.GetV());
      c := a;
      WriteLn(c.GetV());
      a.Free(); b.Free()
    end.
    ''';

procedure TE2EGenericsTests.TestRun_GenericRef_MixedCaseSpellings_OneType;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMixedCaseGeneric, '11' + LE + '22' + LE + '11' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_IntAndString;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncIntStr, '7' + LE + 'yes' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_TypedLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncTypedLocal, '8' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_ParamlessTypedLocalReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncParamlessLocal, '0' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_TwoTypedLocals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncTwoLocals, '42' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericClass_GetSet;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassGetSet, '99' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericRecord_Fields;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordFields, '42' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericClass_MethodTypedLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassMethodLocal, '33' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericRecord_TwoTypeParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordTwoParams, 'age=40' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericClass_DistinctInstantiations;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDistinctInst, '5 hi' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_NestedGeneric_TBoxOfTBox;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedBox, '7' + LE, 0);
end;

const
  SrcClassLocalLikeParam = '''
    program Prg;
    type TB<T> = class
      V: T;
      function R: T; var t: T; begin t := V; Result := t end;
    end;
    var b: TB<Integer>;
    begin b := TB<Integer>.Create(); b.V := 7; WriteLn(b.R()); b.Free() end.
    ''';

  SrcRecordLocalLikeParam = '''
    program Prg;
    type TW<T> = record
      V: T;
      function R: T; var t: T; begin t := V; Result := t end;
    end;
    var w: TW<Integer>;
    begin w.V := 55; WriteLn(w.R()) end.
    ''';

procedure TE2EGenericsTests.TestRun_GenericClass_LocalNamedLikeTypeParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassLocalLikeParam, '7' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericRecord_LocalNamedLikeTypeParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordLocalLikeParam, '55' + LE, 0);
end;

const
  SrcInheritGenericMethodField = '''
    program P;
    type
      TBox<T> = class
        FVal: T;
        procedure SetIt(v: T); begin FVal := v; end;
        function GetIt: T; begin Result := FVal; end;
      end;
      TIntBox = class(TBox<Integer>) end;
    var b: TIntBox;
    begin
      b := TIntBox.Create;
      b.SetIt(7);
      WriteLn(b.GetIt());
      WriteLn(b.FVal);
      b := nil
    end.
    ''';

  SrcInheritGenericVirtual = '''
    program P;
    type
      TBase<T> = class
        function Describe: string; virtual; begin Result := 'base' end;
        function Wrap: string; begin Result := '[' + Self.Describe() + ']' end;
      end;
      TIntD = class(TBase<Integer>)
        function Describe: string; override; begin Result := 'derived' end;
      end;
    var d: TBase<Integer>;
    begin
      d := TIntD.Create;
      WriteLn(d.Wrap());
      d := nil
    end.
    ''';

procedure TE2EGenericsTests.TestRun_InheritFromGenericInstance_MethodAndField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritGenericMethodField, '7' + LE + '7' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_InheritFromGenericInstance_VirtualOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritGenericVirtual, '[derived]' + LE, 0);
end;

const
  SrcGenericImplementsIntf = '''
    program P;
    type
      IVal = interface function Get: Integer; end;
      TBox<T> = class(IVal)
        FV: Integer;
        constructor Create(v: Integer); begin FV := v end;
        function Get: Integer; begin Result := FV end;
      end;
    var iv: IVal;
    begin
      iv := TBox<Integer>.Create(77);
      WriteLn(iv.Get());
      iv := nil
    end.
    ''';

  SrcGenericImplementsIntfArgs = '''
    program P;
    type
      IAdder = interface function Add(a, b: Integer): Integer; end;
      TCalc<T> = class(IAdder)
        function Add(a, b: Integer): Integer; begin Result := a + b end;
      end;
    var ad: IAdder;
    begin
      ad := TCalc<Integer>.Create;
      WriteLn(ad.Add(15, 27));
      ad := nil
    end.
    ''';

procedure TE2EGenericsTests.TestRun_GenericClassImplementsInterface;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericImplementsIntf, '77' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericClassImplementsInterface_MethodArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericImplementsIntfArgs, '42' + LE, 0);
end;

const
  SrcGenMethodPick = '''
    program Prog;
    type
      TUtil = class
        function Pick<T>(cond: Boolean; a, b: T): T;
          begin if cond then Result := a else Result := b end;
      end;
    var u: TUtil;
    begin
      u := TUtil.Create;
      WriteLn(u.Pick<Integer>(True, 7, 9));
      WriteLn(u.Pick<Integer>(False, 7, 9));
      u := nil
    end.
    ''';

  SrcGenMethodTwo = '''
    program Prog;
    type
      TUtil = class
        function Echo<T>(x: T): T; begin Result := x end;
      end;
    var u: TUtil;
    begin
      u := TUtil.Create;
      WriteLn(u.Echo<Integer>(42));
      WriteLn(u.Echo<string>('hi'));
      u := nil
    end.
    ''';

  SrcGenMethodSelf = '''
    program Prog;
    type
      TBox = class
        FBase: Integer;
        constructor Create(b: Integer); begin FBase := b end;
        function Combine<T>(x: T): T; begin Result := x end;
        function Offset: Integer; begin Result := FBase end;
      end;
    var b: TBox;
    begin
      b := TBox.Create(100);
      WriteLn(b.Combine<Integer>(5) + b.Offset());
      b := nil
    end.
    ''';

  SrcGenMethodTwoParams = '''
    program Prog;
    type
      TUtil = class
        function First<A, B>(x: A; y: B): A; begin Result := x end;
      end;
    var u: TUtil;
    begin
      u := TUtil.Create;
      WriteLn(u.First<Integer, string>(7, 'ignored'));
      u := nil
    end.
    ''';

procedure TE2EGenericsTests.TestRun_GenericMethod_Pick;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenMethodPick, '7' + LE + '9' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericMethod_TwoInstantiations;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenMethodTwo, '42' + LE + 'hi' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericMethod_UsesSelfField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenMethodSelf, '105' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericMethod_TwoTypeParams;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenMethodTwoParams, '7' + LE, 0);
end;

const
  { Out-of-line implementation form: the body lives outside the class. }
  SrcGenMethodOutOfLine = '''
    program Prog;
    type
      TUtil = class
        function Pick<T>(cond: Boolean; a, b: T): T;
      end;
    function TUtil.Pick<T>(cond: Boolean; a, b: T): T;
    begin if cond then Result := a else Result := b end;
    var u: TUtil;
    begin
      u := TUtil.Create;
      WriteLn(u.Pick<string>(True, 'aa', 'bb'));
      WriteLn(u.Pick<Integer>(False, 1, 2));
      u := nil
    end.
    ''';

procedure TE2EGenericsTests.TestRun_GenericMethod_OutOfLineImpl;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenMethodOutOfLine, 'aa' + LE + '2' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Open-array parameters with a generic element type                    }
{ ------------------------------------------------------------------ }

procedure TE2EGenericsTests.TestRun_GenericOpenArray_ElementTypeIsT;
begin
  { `array of T` must substitute T at instantiation.  It used to leave the
    ELEMENT type unresolved -- it fell back to Integer -- so indexing the
    array in a TBox<string> reported 'expected string but got Integer'.
    Plain T parameters were always substituted correctly; only the nested
    element type was missed. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TBox<T> = class
        procedure Probe(const AItems: array of T);
      end;
    procedure TBox<T>.Probe(const AItems: array of T);
    var V: T;
    begin
      V := AItems[0];
      WriteLn(V)
    end;
    var B: TBox<string>;
    begin
      B := TBox<string>.Create();
      B.Probe(['hello', 'world'])
    end.
    ''', 'hello' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericOpenArray_PassesElementToTMethod;
begin
  { The indirect shape: an element read from `array of T` is handed to a
    method taking T.  This is what AddAll/AddRange on a generic collection
    needs, and it failed with 'No matching overload ... with 1 argument(s)'
    because the element typed as Integer. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TBox<T> = class
        FAcc: string;
        procedure Add(const V: T);
        procedure AddAll(const AItems: array of T);
      end;
    procedure TBox<T>.Add(const V: T);
    begin
      FAcc := FAcc + V
    end;
    procedure TBox<T>.AddAll(const AItems: array of T);
    var I: Integer;
    begin
      for I := Low(AItems) to High(AItems) do
        Self.Add(AItems[I])
    end;
    var B: TBox<string>;
    begin
      B := TBox<string>.Create();
      B.AddAll(['a', 'b', 'c']);
      WriteLn(B.FAcc)
    end.
    ''', 'abc' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericOpenArray_StaticFactory;
begin
  { The motivating case: a static factory on the generic itself, taking a
    bracket literal.  This is the shape TSet<T>.From uses. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TBox<T> = class
        FN: Integer;
        FFirst: T;
        static function From(const AItems: array of T): TBox<T>;
      end;
    static function TBox<T>.From(const AItems: array of T): TBox<T>;
    begin
      Result := TBox<T>.Create();
      Result.FN := High(AItems) - Low(AItems) + 1;
      if Result.FN > 0 then
        Result.FFirst := AItems[0]
    end;
    var B: TBox<string>;
    begin
      B := TBox<string>.From(['x', 'y', 'z']);
      WriteLn(B.FN);
      WriteLn(B.FFirst)
    end.
    ''', '3' + LE + 'x' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericOpenArray_TwoInstantiations;
begin
  { Two instantiations of the same generic must each get their OWN element
    type -- a fix that substituted once and cached would pass the single-
    instantiation tests above and fail here. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TBox<T> = class
        procedure First(const AItems: array of T);
      end;
    procedure TBox<T>.First(const AItems: array of T);
    var V: T;
    begin
      V := AItems[0];
      WriteLn(V)
    end;
    var
      S: TBox<string>;
      N: TBox<Integer>;
    begin
      S := TBox<string>.Create();
      N := TBox<Integer>.Create();
      S.First(['str']);
      N.First([42])
    end.
    ''', 'str' + LE + '42' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Member visibility across a generic import                            }
{ ------------------------------------------------------------------ }

procedure TE2EGenericsTests.TestRun_GenericImport_PrivateMethodIsRejected;
var
  Output: string;
  RCode:  Int;
  Ok:     Boolean;
begin
  { A `private` method on a generic was callable from any importing unit,
    while the same method on a NON-generic class was correctly rejected.
    Two causes, both needed: ReadGenericClassPayload rebuilt the method decl
    without Visibility, and the instantiated decl's OwningUnit names the
    ANALYSING compilation (deliberately — every unit that touches TFoo<Bar>
    materialises it and they must agree on one bare symbol), which
    MemberVisibleTo then read as same-unit.  VisibilityUnit carries the
    TEMPLATE's declaring unit for the check.

    Must reach the compiler, not just the harness: this test asserts the
    compile FAILS, with the access diagnostic. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Ok := CompileAndRunWithUnit('gvis',
      '''
      unit gvis;
      interface
      type
        TGuard<T> = class
        private
          procedure Hidden;
        public
          procedure Shown;
        end;
      implementation
      procedure TGuard<T>.Hidden;
      begin WriteLn('hidden') end;
      procedure TGuard<T>.Shown;
      begin WriteLn('shown') end;
      end.
      ''',
      '''
      program P;
      uses gvis;
      var G: TGuard<string>;
      begin
        G := TGuard<string>.Create();
        G.Hidden()
      end.
      ''', Output, RCode);
  AssertFalse('calling a private method on an imported generic must not compile',
              Ok);
  AssertTrue('the diagnostic names the access violation, got: ' + Output,
             Pos('''Hidden'' is not accessible', Output) >= 0);
end;

procedure TE2EGenericsTests.TestRun_GenericImport_PublicMethodStillReachable;
begin
  { The other half — the fix must not lock out legitimate public access. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TGuard<T> = class
      private
        procedure Hidden;
      public
        procedure Shown;
      end;
    procedure TGuard<T>.Hidden;
    begin WriteLn('hidden') end;
    procedure TGuard<T>.Shown;
    begin WriteLn('shown') end;
    var G: TGuard<string>;
    begin
      G := TGuard<string>.Create();
      G.Shown()
    end.
    ''', 'shown' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_StackQueueList_OrderAcrossGrow;
const
  {
    TStack<Integer> pops LIFO and TQueue<Integer> dequeues FIFO, each across a
    Grow (10 elements, initial capacity 4); Peek does not remove; TList<Integer>
    holds 20 elements across its Grow.  Replaces the QBE IR checks in
    cp.test.tstack, cp.test.tqueue and cp.test.tlist. }
  Src = '''
    program P;
    uses Generics.Collections;
    var S: TStack<Integer>; Q: TQueue<Integer>; L: TList<Integer>; I: Integer;
    begin
      S := TStack<Integer>.Create();
      for I := 1 to 10 do
        S.Push(I * 10);
      Write(S.Count, ' ', S.Peek(), ' ', S.Count, ':');
      while not S.IsEmpty() do
        Write(' ', S.Pop());
      WriteLn('');
      Q := TQueue<Integer>.Create();
      for I := 1 to 10 do
        Q.Enqueue(I);
      Write(Q.Count, ' ', Q.Peek(), ' ', Q.Count, ':');
      while not Q.IsEmpty() do
        Write(' ', Q.Dequeue());
      WriteLn('');
      L := TList<Integer>.Create();
      for I := 0 to 19 do
        L.Add(I * I);
      WriteLn(L.Count, ' ', L[0], ' ', L[19], ' ', L[7])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '10 100 10: 100 90 80 70 60 50 40 30 20 10' + LE +
    '10 1 10: 1 2 3 4 5 6 7 8 9 10' + LE +
    '20 0 361 49' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TSet_IncludeExcludeContains;
const
  {
    TSet<Integer> ignores duplicate Includes, Excludes a member (and a
    non-member harmlessly), and answers Contains, across a Grow and hash rebuild
    (20 elements).  Replaces the QBE IR checks in cp.test.tset. }
  Src = '''
    program P;
    uses Generics.Collections;
    var S: TSet<Integer>; I, N: Integer;
    begin
      S := TSet<Integer>.Create();
      for I := 1 to 20 do
        S.Include(I);
      S.Include(5);
      S.Include(20);
      WriteLn(S.Count, ' ', S.Contains(7), ' ', S.Contains(21));
      S.Exclude(7);
      S.Exclude(99);
      N := 0;
      for I := 1 to 20 do
        if S.Contains(I) then
          N := N + 1;
      WriteLn(S.Count, ' ', S.Contains(7), ' ', N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '20 True False' + LE +
    '19 False 19' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TDictionary_AddLookupUpdateRemove;
const
  {
    TDictionary<Integer, Integer>: Add across a Grow, the default property read
    and write, ContainsKey, TryGetValue hit and miss, and Remove.  Replaces the QBE
    IR checks in cp.test.tdictionary. }
  Src = '''
    program P;
    uses Generics.Collections;
    var D: TDictionary<Integer, Integer>; I, V: Integer;
    begin
      D := TDictionary<Integer, Integer>.Create();
      for I := 1 to 20 do
        D.Add(I, I * 100);
      WriteLn(D.Count, ' ', D[5], ' ', D[20]);
      D[5] := 7;
      WriteLn(D[5], ' ', D.ContainsKey(5), ' ', D.ContainsKey(21));
      if D.TryGetValue(12, V) then
        WriteLn('got ', V);
      if not D.TryGetValue(42, V) then
        WriteLn('no 42');
      D.Remove(12);
      WriteLn(D.Count, ' ', D.ContainsKey(12), ' ', D[13])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '20 500 2000' + LE +
    '7 True False' + LE +
    'got 1200' + LE +
    'no 42' + LE +
    '19 False 1300' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TOrderedDictionary_KeepsInsertionOrder;
const
  {
    TOrderedDictionary keeps insertion order through GetKey/GetValue, an update
    through the default property keeps the key's position, and Remove/TryGetValue
    work.  Replaces the QBE IR checks in cp.test.tordereddictionary. }
  Src = '''
    program P;
    uses Generics.Collections;
    var D: TOrderedDictionary<Integer, Integer>; I, V: Integer;
    begin
      D := TOrderedDictionary<Integer, Integer>.Create();
      D.Add(30, 3);
      D.Add(10, 1);
      D.Add(20, 2);
      for I := 0 to D.Count - 1 do
        Write(D.GetKey(I), '=', D.GetValue(I), ' ');
      WriteLn('');
      D[10] := 11;
      for I := 0 to D.Count - 1 do
        Write(D.GetKey(I), '=', D.GetValue(I), ' ');
      WriteLn('');
      D.Remove(30);
      if D.TryGetValue(20, V) then
        WriteLn(D.Count, ' ', V, ' ', D.ContainsKey(30))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '30=3 10=1 20=2 ' + LE +
    '30=3 10=11 20=2 ' + LE +
    '2 2 False' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_IMap_OneCallSiteBothImplementations;
const
  {
    One IMap<Integer, Integer> call site drives both TDictionary and
    TOrderedDictionary through their interface tables: Add, Remove, TryGetValue,
    ContainsKey, GetCount.  Replaces the QBE IR checks in cp.test.imap (typeinfo,
    itab, impllist, indirect dispatch). }
  Src = '''
    program P;
    uses Generics.Collections;
    procedure Fill(M: IMap<Integer, Integer>; const Tag: string);
    var V: Integer;
    begin
      M.Add(1, 10);
      M.Add(2, 20);
      M.Add(3, 30);
      M.Remove(2);
      V := 0;
      if M.TryGetValue(3, V) then
        WriteLn(Tag, ' ', M.GetCount(), ' ', V, ' ', M.ContainsKey(2), ' ', M.ContainsKey(1));
    end;
    begin
      Fill(TDictionary<Integer, Integer>.Create(), 'dict');
      Fill(TOrderedDictionary<Integer, Integer>.Create(), 'ordered')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'dict 2 30 False True' + LE +
    'ordered 2 30 False True' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericForIn_UserEnumerator;
const
  {
    for X in L over a user generic list calls its generic enumerator's
    GetEnumerator, MoveNext and Current.  Replaces the QBE IR checks in
    cp.test.genericforin. }
  Src = '''
    program P;
    type
      TListEnumerator<T> = class
        FList:  ^T;
        FIndex: Integer;
        FCount: Integer;
        function MoveNext: Boolean;
        begin
          Self.FIndex := Self.FIndex + 1;
          Result := Self.FIndex < Self.FCount
        end;
        function GetCurrent: T;
        begin
          Result := (Self.FList + Self.FIndex * SizeOf(T))^
        end;
        property Current: T read GetCurrent;
      end;
      TMyList<T> = class
        FData:  ^T;
        FCount: Integer;
        procedure Add(V: T);
        var Slot: ^T;
        begin
          Self.FData := ReallocMem(Self.FData, (Self.FCount + 1) * SizeOf(T));
          Slot := Self.FData + Self.FCount * SizeOf(T);
          Slot^ := V;
          Self.FCount := Self.FCount + 1
        end;
        function GetEnumerator: TListEnumerator<T>;
        begin
          Result := TListEnumerator<T>.Create();
          Result.FList := Self.FData;
          Result.FIndex := -1;
          Result.FCount := Self.FCount
        end;
      end;
    var
      L: TMyList<Integer>;
      X: Integer;
    begin
      L := TMyList<Integer>.Create();
      L.Add(4);
      L.Add(8);
      L.Add(15);
      for X in L do
        Write(X, ' ');
      WriteLn('|')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4 8 15 |' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TwoInstances_SelfCallReachesOwnInstance;
const
  {
    Two instances of one generic class side by side: a method of each instance
    that calls another method through Self must reach ITS OWN instance's body
    (TBox<Integer>.Init -> TBox<Integer>.SetValue, TBox<string>.Init ->
    TBox<string>.SetValue), each storing into its own field type. }
  Src = '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
        procedure SetValue(V: T);
        begin
          Self.FValue := V
        end;
        procedure Init(V: T);
        begin
          Self.SetValue(V)
        end;
        function GetValue: T;
        begin
          Result := Self.FValue
        end;
      end;
    var
      A: TBox<Integer>;
      B: TBox<string>;
    begin
      A := TBox<Integer>.Create();
      B := TBox<string>.Create();
      A.Init(42);
      B.Init('forty-two');
      WriteLn(A.GetValue(), ' ', B.GetValue())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '42 forty-two' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TDictionary_DynArrayValue;
const
  { GH #220: a dyn-array VALUE type.  x86-64 first failed to link (the
    IMap<string, array of Byte> typeinfo was never emitted, fixed by
    fbd36994); arm64 then could not store a dyn array into TryGetValue's
    out param or the entry fields. }
  Src = '''
    program P;
    uses Generics.Collections;
    type
      TBytes = array of Byte;
    var
      D: TDictionary<string, TBytes>;
      A, V: TBytes;
    begin
      D := TDictionary<string, TBytes>.Create();
      SetLength(A, 2);
      A[1] := 9;
      D.Add('a', A);
      SetLength(A, 3);
      D['b'] := A;
      WriteLn(D['a'][1], ' ', Length(D['b']));
      if D.TryGetValue('a', V) then
        WriteLn('got ', Length(V), ' ', V[1]);
      D.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '9 3' + LE + 'got 2 9' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_ArrayOfTypeParamFields;
const
  Src = '''
    program P;
    type
      TBox<T> = class
        FItems: array of T;
        FFix: array[0..1] of T;
        FNest: array of array of T;
        procedure Add(const V: T);
      end;
      TRB<T> = record
        D: array of T;
      end;
    procedure TBox<T>.Add(const V: T);
    begin
      SetLength(FItems, Length(FItems) + 1);
      FItems[High(FItems)] := V;
      FFix[1] := V;
      SetLength(FNest, 1);
      FNest[0] := FItems
    end;
    var
      B: TBox<string>;
      R: TRB<Integer>;
    begin
      B := TBox<string>.Create();
      B.Add('x');
      B.Add('y');
      WriteLn(Length(B.FItems), B.FItems[1], B.FFix[1], Length(B.FNest[0]));
      SetLength(R.D, 3);
      R.D[2] := 7;
      WriteLn(R.D[2])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2yy2' + LE + '7' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericTypeOverloads;
const
  UnitSrc = '''
    unit gover;
    interface
    type
      TBase<T> = class
        FV: T;
        constructor Create(); overload;
        constructor Create(const A: T); overload;
        function Describe(): string; overload; virtual;
        function Describe(const P: string): string; overload; virtual;
      end;
      TKid<T> = class(TBase<T>)
        function Describe(const P: string): string; overload; override;
      end;
      TPair<T> = record
        A: T;
        function Get(): T; overload;
        function Get(D: Integer): Integer; overload;
      end;
      TBox<T> = class
        procedure Put(A: T); overload;
        procedure Put(A: Integer); overload;
      end;
    implementation
    constructor TBase<T>.Create(); begin end;
    constructor TBase<T>.Create(const A: T); begin FV := A end;
    function TBase<T>.Describe(): string; begin Result := 'base0' end;
    function TBase<T>.Describe(const P: string): string; begin Result := 'base1 ' + P end;
    function TKid<T>.Describe(const P: string): string; begin Result := 'kid ' + P end;
    function TPair<T>.Get(): T; begin Result := A end;
    function TPair<T>.Get(D: Integer): Integer; begin Result := D * 2 end;
    procedure TBox<T>.Put(A: T); begin WriteLn('T') end;
    procedure TBox<T>.Put(A: Integer); begin WriteLn('Int') end;
    end.
    ''';
  Src = '''
    program UseGOver;
    uses gover;
    var B: TBase<string>; K: TBase<Integer>; P: TPair<string>;
      BS: TBox<string>; BI: TBox<Integer>;
    begin
      B := TBase<string>.Create('hi');
      WriteLn(B.FV, ' ', B.Describe(), ' ', B.Describe('x'));
      K := TKid<Integer>.Create(7);
      WriteLn(K.FV, ' ', K.Describe(), ' ', K.Describe('y'));
      K := TKid<Integer>.Create();
      WriteLn(K.FV);
      P.A := 'pa';
      WriteLn(P.Get(), ' ', P.Get(21));
      BS := TBox<string>.Create();
      BS.Put('a');
      BS.Put(1);
      BI := TBox<Integer>.Create();
      WriteLn(BI <> nil)
    end.
    ''';
var
  Output: string;
  ExitCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile + run', CompileAndRunWithUnit('gover', UnitSrc, Src,
    Output, ExitCode));
  AssertEquals('exit code', 0, ExitCode);
  AssertEquals('stdout', 'hi base0 base1 x' + #10 + '7 base0 kid y' + #10 +
    '0' + #10 + 'pa 42' + #10 + 'T' + #10 + 'Int' + #10 + 'True' + #10,
    Output);
end;

procedure TE2EGenericsTests.TestRun_Dictionary_NumericAndStaticArrayTypeArgs;
const
  Src = '''
    program P;
    uses Generics.Collections;
    type
      Tar = array[0..3] of Integer;
      TNeg = array[-2..1] of string;
    var
      D1: TDictionary<Byte, Tar>;
      D2: TDictionary<Byte, Integer>;
      D3: TDictionary<Integer, TNeg>;
      A: Tar;
      N: TNeg;
      X: Byte;
    begin
      D1 := TDictionary<Byte, Tar>.Create();
      for X := 0 to 4 do
      begin
        A[3] := X * 10;
        D1.Add(X, A)
      end;
      for X := 0 to 4 do
      begin
        A := D1[X];
        Write(A[3], ' ')
      end;
      WriteLn();
      D2 := TDictionary<Byte, Integer>.Create();
      for X := 0 to 4 do
        D2.Add(X, 32 * X);
      WriteLn(D2[4]);
      D3 := TDictionary<Integer, TNeg>.Create();
      N[-2] := 'lo';
      N[1] := 'hi';
      D3.Add(-7, N);
      WriteLn(D3[-7][-2], ' ', D3[-7][1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0 10 20 30 40 ' + LE + '128' + LE + 'lo hi' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_CalledTwice;
const
  Src = '''
    program P;
    function Twice<T>(a: T): T;
    begin
      Result := a + a
    end;
    var I: Integer; S: string;
    begin
      I := Twice<Integer>(4);
      I := Twice<Integer>(I);
      S := Twice<string>('ab');
      WriteLn(I, ' ', Twice<Integer>(1), ' ', S, ' ', Twice<string>(S))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '16 2 abab abababab' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericProcedure_CalledAsStatement;
const
  Src = '''
    program P;
    type
      TPair<K, V> = record Key: K; Val: V; end;
    procedure GenericProc<T>(a, b: T);
    begin
      WriteLn(a, ' ', b)
    end;
    procedure Swap<T>(var a, b: T);
    var t: T;
    begin
      t := a; a := b; b := t
    end;
    function Twice<T>(a: T): T;
    begin
      Result := a + a
    end;
    procedure Show<K, V>(const P: TPair<K, V>);
    begin
      WriteLn(P.Key, '=', P.Val)
    end;
    var X, Y: Integer; S1, S2: string; Pr: TPair<string, Integer>;
    begin
      GenericProc<Integer>(10, 11);
      GenericProc<string>('x', 'y');
      X := 1; Y := 2;
      Swap<Integer>(X, Y);
      S1 := 'a'; S2 := 'b';
      Swap<string>(S1, S2);
      WriteLn(X, Y, S1, S2);
      Twice<Integer>(4);
      WriteLn(Twice<Integer>(4));
      Pr.Key := 'k'; Pr.Val := 9;
      Show<string, Integer>(Pr);
      if X > 1 then GenericProc<Integer>(7, 8)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '10 11' + LE + 'x y' + LE + '21ba' + LE + '8' + LE +
    'k=9' + LE + '7 8' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_GenericFunc_BodyUsesTypeParam;
const
  Src = '''
    program P;
    uses Generics.Collections;
    type
      TBox<T> = class
        Items: TList<T>;
        constructor Create(A: TList<T>);
      end;
    constructor TBox<T>.Create(A: TList<T>);
    begin
      Items := A
    end;
    function Wrap<T>(A: TList<T>): TBox<T>;
    begin
      Result := TBox<T>.Create(A)
    end;
    function Single<T>(V: T): TList<T>;
    begin
      Result := TList<T>.Create();
      Result.Add(V)
    end;
    function Size<T>(): Integer;
    begin
      Result := SizeOf(T)
    end;
    var L: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(5); L.Add(6);
      WriteLn(Wrap<Integer>(L).Items.Count);
      WriteLn(Single<string>('s')[0]);
      WriteLn(Size<Int64>(), ' ', Size<Byte>())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2' + LE + 's' + LE + '8 1' + LE, 0);
end;

procedure TE2EGenericsTests.TestRun_TypeParamCast_EveryIntegerKind;
const
  Src = '''
    program P;
    type
      TColour = (cRed, cGreen, cBlue);
      TConv<T> = class
        function Conv(X: Int64): T;
      end;
    function TConv<T>.Conv(X: Int64): T;
    begin
      Result := T(X)
    end;
    function Conv<T>(X: Int64): T;
    begin
      Result := T(X)
    end;
    begin
      WriteLn(TConv<Byte>.Create().Conv(300), ' ',
              TConv<Int8>.Create().Conv(200), ' ',
              TConv<SmallInt>.Create().Conv(40000), ' ',
              TConv<Word>.Create().Conv(70000));
      WriteLn(TConv<Integer>.Create().Conv(4294967297), ' ',
              TConv<UInt32>.Create().Conv(-1), ' ',
              TConv<Int64>.Create().Conv(-5), ' ',
              TConv<UInt64>.Create().Conv(4294967297), ' ',
              Ord(TConv<TColour>.Create().Conv(2)));
      WriteLn(Conv<Byte>(300), ' ', Conv<Int8>(200), ' ',
              Conv<SmallInt>(40000), ' ', Conv<Word>(70000));
      WriteLn(Conv<Integer>(4294967297), ' ', Conv<UInt32>(-1), ' ',
              Conv<Int64>(-5), ' ', Conv<UInt64>(4294967297), ' ',
              Ord(Conv<TColour>(2)))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '44 -56 -25536 4464' + LE + '1 4294967295 -5 4294967297 2' + LE +
    '44 -56 -25536 4464' + LE + '1 4294967295 -5 4294967297 2' + LE, 0);
end;

initialization
  RegisterTest(TE2EGenericsTests);

end.
