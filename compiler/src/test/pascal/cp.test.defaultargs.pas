{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.defaultargs;

{ Default parameters must be materialised into the call's argument list by
  the semantic pass for EVERY call form.  AnalyseMethodCall (method call
  STATEMENTS) didn't append them: the emitted call then carried fewer
  arguments than the callee's parameter list, and the callee read garbage
  for the missing ones — caller-frame junk once the parameter fell past
  the six SysV registers.  Found 2026-06-10 via the borrowed-local elision
  crash (native EmitInterfaceCall read its stack-passed AObjExpr=nil
  default from an argument slot the caller never wrote). }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TDefaultArgsTests = class(TTestCase)
  private
  published
    { a FUNCTION method called through a receiver (Self.F(1), X.F(1)), a
      generic method, and an inherited call -- statement or expression --
      fill omitted trailing arguments from the declared defaults, as a bare
      F(1) and a procedure statement already did; they reported "expects 2
      argument(s) but got 1" }
    procedure TestSemantic_DefaultArgs_EveryMethodCallForm;
    { a set-constant default ([], [mShift]) is accepted; a variable element
      is not, since the literal is substituted at every call site }
    procedure TestSemantic_SetDefault_ConstantsAccepted;
    procedure TestSemantic_SetDefault_VariableElementRejected;
    { [Weak] on a generic class field whose instance type is not a class or
      interface is rejected at instantiation, at the field's position }
    procedure TestSemantic_WeakGenericField_NonClassInstanceRejected;
  end;

implementation

procedure TDefaultArgsTests.TestSemantic_DefaultArgs_EveryMethodCallForm;
const
  Head = '''
    program P;
    type
      TBase = class
        function F(A: Int32; B: Int32 = 5): Int32; virtual;
        procedure Q(A: Int32; B: Int32 = 5); virtual;
      end;
      TA = class(TBase)
        function F(A: Int32; B: Int32 = 5): Int32; override;
        procedure Q(A: Int32; B: Int32 = 5); override;
        function G<T>(A: T; B: Int32 = 7): Int32;
        procedure Run();
      end;
    var X: TA; N: Int32;
    function TBase.F(A: Int32; B: Int32): Int32; begin Result := A + B end;
    procedure TBase.Q(A: Int32; B: Int32); begin end;
    function TA.G<T>(A: T; B: Int32): Int32; begin Result := B end;
    ''';
begin
  AssertEquals('Self.F(1)', '', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; begin Result := Self.F(1) end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin end; ' +
    'procedure TA.Run(); begin end; begin end.'));
  AssertEquals('X.F(1)', '', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; begin Result := A end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin end; ' +
    'procedure TA.Run(); begin end; begin N := X.F(1) end.'));
  AssertEquals('X.G<Int32>(1)', '', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; begin Result := A end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin end; ' +
    'procedure TA.Run(); begin end; begin N := X.G<Int32>(1) end.'));
  AssertEquals('inherited F(1) as an expression', '', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; ' +
    '  begin Result := inherited F(A) end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin end; ' +
    'procedure TA.Run(); begin end; begin end.'));
  AssertEquals('inherited Q(1) as a statement', '', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; begin Result := A end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin inherited Q(A) end; ' +
    'procedure TA.Run(); begin end; begin end.'));
  AssertTrue('a missing argument with no default still fails',
    Pos('TA.F', SemanticError(Head +
    'function TA.F(A: Int32; B: Int32): Int32; begin Result := A end; ' +
    'procedure TA.Q(A: Int32; B: Int32); begin end; ' +
    'procedure TA.Run(); begin end; begin N := X.F() end.')) >= 0);
end;

procedure TDefaultArgsTests.TestSemantic_SetDefault_ConstantsAccepted;
const
  Src = '''
    program P;
    type
      TMod = (mShift, mCtrl);
      TMods = set of TMod;
    procedure A(M: TMods = []); begin end;
    procedure B(M: TMods = [mShift, mCtrl]); begin end;
    begin
      A();
      B();
    end.
    ''';
begin
  AssertEquals('accepted', '', SemanticError(Src));
end;

procedure TDefaultArgsTests.TestSemantic_SetDefault_VariableElementRejected;
const
  Src = '''
    program P;
    type
      TMod = (mShift, mCtrl);
      TMods = set of TMod;
    var
      V: TMod;
    procedure A(M: TMods = [V]); begin end;
    begin
      A();
    end.
    ''';
var
  Msg: string;
begin
  Msg := SemanticError(Src);
  AssertTrue('rejected: ' + Msg, Pos('must be a set of constants', Msg) >= 0);
end;

procedure TDefaultArgsTests.TestSemantic_WeakGenericField_NonClassInstanceRejected;
const
  Src = '''
    program P;
    type
      TG<T> = class
      public
        [Weak] W: T;
      end;
    var
      G: TG<Int>;
    begin
      G := TG<Int>.Create();
    end.
    ''';
var
  Msg: string;
begin
  Msg := SemanticError(Src);
  AssertTrue('rejected: ' + Msg,
    Pos('[Weak] can only be applied to class or interface fields', Msg) >= 0);
  AssertTrue('at the field: ' + Msg, Pos('line 5', Msg) >= 0);
end;

initialization
  RegisterTest(TDefaultArgsTests);

end.
