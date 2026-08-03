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

initialization
  RegisterTest(TE2EGenericsTests);

end.
