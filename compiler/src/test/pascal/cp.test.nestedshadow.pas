{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nestedshadow;

{ A routine nested inside another routine may carry the name of a built-in
  routine (Length, Copy, Sqrt, SetLength, ...).  A call to it is a call of
  that routine: the analyser and both backends recognise built-ins by name,
  and before BUG-20261113-nested-builtin-routine-shadow-ignored they lowered
  such a call as the built-in, silently.  These tests pin that each call
  shape -- integer, string and float results, and a procedure -- reaches the
  nested routine's symbol on both ISAs; cp.test.e2e.nestedshadow runs it. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness;

type
  TNestedShadowTests = class(TTestCase)
  published
    procedure TestLength_IntResult_CallsNestedRoutine;
    procedure TestAbsAndOrd_CallNestedRoutine;
    procedure TestCopy_StringResult_CallsNestedRoutine;
    procedure TestSqrt_FloatResult_CallsNestedRoutine;
    procedure TestSetLength_Procedure_CallsNestedRoutine;
    procedure TestNestedRoutine_ArgumentsCheckedAgainstIt;
    { BUG-20261128-x86-builtin-replaces-self-method: a method named like a
      built-in, called on the implicit Self, is that method.  x86-64 lowered
      it as the built-in (arm64 checked ResolvedDecl itself), so PasBuild's
      test fixture helper WriteFile never ran on Linux or Windows x86-64. }
    procedure TestSelfMethod_ProcedureNamedLikeBuiltin_CallsMethod;
    procedure TestSelfMethod_FunctionNamedLikeBuiltin_CallsMethod;
  end;

implementation

const
  SrcLength =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Length(const S: string): Int32;'#10 +
    '  begin'#10 +
    '    Result := 99;'#10 +
    '  end;'#10 +
    'var N: Int32;'#10 +
    'begin'#10 +
    '  N := Length(''abc'');'#10 +
    '  WriteLn(N);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;

procedure TNestedShadowTests.TestLength_IntResult_CallsNestedRoutine;
begin
  AssertEquals('', AsmMissing(SrcLength, 'callq Outer_Length',
    'bl _Outer_Length'));
end;

procedure TNestedShadowTests.TestAbsAndOrd_CallNestedRoutine;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Abs(X: Int32): Int32;'#10 +
    '  begin'#10 +
    '    Result := 1000;'#10 +
    '  end;'#10 +
    '  function Ord(B: Boolean): Int32;'#10 +
    '  begin'#10 +
    '    Result := 555;'#10 +
    '  end;'#10 +
    'begin'#10 +
    '  WriteLn(Abs(-3), Ord(True));'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;
begin
  AssertEquals('Abs', '', AsmMissing(Src, 'callq Outer_Abs', 'bl _Outer_Abs'));
  AssertEquals('Ord', '', AsmMissing(Src, 'callq Outer_Ord', 'bl _Outer_Ord'));
end;

procedure TNestedShadowTests.TestCopy_StringResult_CallsNestedRoutine;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Copy(const S: string; A, B: Int32): string;'#10 +
    '  begin'#10 +
    '    Result := ''mine'';'#10 +
    '  end;'#10 +
    'var S: string;'#10 +
    'begin'#10 +
    '  S := Copy(''abcdef'', 1, 2);'#10 +
    '  WriteLn(S);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;
begin
  AssertEquals('', AsmMissing(Src, 'callq Outer_Copy', 'bl _Outer_Copy'));
end;

procedure TNestedShadowTests.TestSqrt_FloatResult_CallsNestedRoutine;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  function Sqrt(X: Float64): Float64;'#10 +
    '  begin'#10 +
    '    Result := 42.0;'#10 +
    '  end;'#10 +
    'var D: Float64;'#10 +
    'begin'#10 +
    '  D := Sqrt(4.0);'#10 +
    '  WriteLn(D);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;
begin
  AssertEquals('', AsmMissing(Src, 'callq Outer_Sqrt', 'bl _Outer_Sqrt'));
end;

procedure TNestedShadowTests.TestSetLength_Procedure_CallsNestedRoutine;
const
  Src =
    'program p;'#10 +
    'procedure Outer;'#10 +
    '  procedure SetLength(var S: string; N: Int32);'#10 +
    '  begin'#10 +
    '    S := ''mine'';'#10 +
    '  end;'#10 +
    'var S: string;'#10 +
    'begin'#10 +
    '  SetLength(S, 3);'#10 +
    '  WriteLn(S);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  Outer();'#10 +
    'end.'#10;
begin
  AssertEquals('', AsmMissing(Src, 'callq Outer_SetLength',
    'bl _Outer_SetLength'));
end;

procedure TNestedShadowTests.TestNestedRoutine_ArgumentsCheckedAgainstIt;
begin
  { the nested Length takes two Int32s: the call is checked against it, not
    against the built-in's one-argument rule }
  AssertTrue('argument checked against the nested routine',
    SemanticError(
      'program p;'#10 +
      'procedure Outer;'#10 +
      '  function Length(A, B: Int32): Int32;'#10 +
      '  begin'#10 +
      '    Result := A + B;'#10 +
      '  end;'#10 +
      'var N: Int32;'#10 +
      'begin'#10 +
      '  N := Length(1, 2);'#10 +
      'end;'#10 +
      'begin'#10 +
      '  Outer();'#10 +
      'end.'#10) = '');
end;

procedure TNestedShadowTests.TestSelfMethod_ProcedureNamedLikeBuiltin_CallsMethod;
const
  Src =
    'program p;'#10 +
    'type'#10 +
    '  TFix = class'#10 +
    '    procedure WriteFile(const APath, AText: string);'#10 +
    '    procedure DeleteFile(const APath: string);'#10 +
    '    procedure Run();'#10 +
    '  end;'#10 +
    'procedure TFix.WriteFile(const APath, AText: string);'#10 +
    'begin'#10 +
    '  WriteLn(APath);'#10 +
    'end;'#10 +
    'procedure TFix.DeleteFile(const APath: string);'#10 +
    'begin'#10 +
    '  WriteLn(APath);'#10 +
    'end;'#10 +
    'procedure TFix.Run();'#10 +
    'begin'#10 +
    '  WriteFile(''a'', ''b'');'#10 +
    '  DeleteFile(''a'');'#10 +
    'end;'#10 +
    'begin'#10 +
    '  TFix.Create().Run();'#10 +
    'end.'#10;
begin
  AssertEquals('WriteFile', '', AsmMissing(Src, 'callq TFix_WriteFile',
    'bl _TFix_WriteFile'));
  AssertEquals('DeleteFile', '', AsmMissing(Src, 'callq TFix_DeleteFile',
    'bl _TFix_DeleteFile'));
end;

procedure TNestedShadowTests.TestSelfMethod_FunctionNamedLikeBuiltin_CallsMethod;
const
  Src =
    'program p;'#10 +
    'type'#10 +
    '  TFix = class'#10 +
    '    function ReadFile(const APath: string): string;'#10 +
    '    procedure Run();'#10 +
    '  end;'#10 +
    'function TFix.ReadFile(const APath: string): string;'#10 +
    'begin'#10 +
    '  Result := APath;'#10 +
    'end;'#10 +
    'procedure TFix.Run();'#10 +
    'var S: string;'#10 +
    'begin'#10 +
    '  S := ReadFile(''a'');'#10 +
    '  WriteLn(S);'#10 +
    'end;'#10 +
    'begin'#10 +
    '  TFix.Create().Run();'#10 +
    'end.'#10;
begin
  AssertEquals('', AsmMissing(Src, 'callq TFix_ReadFile', 'bl _TFix_ReadFile'));
end;

initialization
  RegisterTest(TNestedShadowTests);

end.
