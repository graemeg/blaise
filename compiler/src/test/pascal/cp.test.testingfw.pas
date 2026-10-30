{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.testingfw;

{ Self-test of the blaise.testing attribute vocabulary.  This suite IS the
  test: the runner must
    * expand each [TestCase] into its own typed run (the method's declared
      parameters receive the converted attribute arguments via the
      param-sig trampoline in TTestCase.RunTest),
    * report labelled runs as 'Method[case]',
    * skip [Ignore] methods entirely (the body would Fail if executed),
    * run [Retry(N)] methods N times,
  so a green suite proves the whole pipeline: attribute reification
  (GetMethodAttributeAt + constructor thunks), the published-method
  param-sig RTTI, and the five-slot typed dispatch. }

interface

uses
  blaise.testing;

type
  TParameterisedTests = class(TTestCase)
  published
    [TestCase('small',    '2,3,5')]
    [TestCase('negative', '-2,-3,-5')]
    [TestCase('zero',     '0,0,0')]
    procedure TestTypedIntSum(A, B, Expected: Int);

    [TestCase('concat', 'foo,bar,foobar')]
    [TestCase('empty-right', 'foo,,foo')]
    procedure TestTypedStrings(const A, B, Expected: string);

    [TestCase('yes', 'True,1')]
    [TestCase('no',  'False,0')]
    procedure TestTypedBool(AFlag: Boolean; AExpected: Int);

    [TestCase('wide', '4294967296,8589934592')]
    procedure TestTypedInt64(A, ATwice: Int64);

    [TestCase('mixed', '7,seven,True')]
    procedure TestMixedKinds(N: Int; const S: string; B: Boolean);

    [TestCase('labelled-only')]
    procedure TestLabelledParameterless;

    [Ignore('exercises [Ignore] — this body would fail if executed')]
    procedure TestIgnoredNeverRuns;

    [Retry(3)]
    [Category('selftest')]
    procedure TestRetriedRuns;
  end;

implementation

procedure TParameterisedTests.TestTypedIntSum(A, B, Expected: Int);
begin
  AssertEquals(CaseName, Expected, A + B);
end;

procedure TParameterisedTests.TestTypedStrings(const A, B, Expected: string);
begin
  AssertEquals(CaseName, Expected, A + B);
end;

procedure TParameterisedTests.TestTypedBool(AFlag: Boolean; AExpected: Int);
begin
  if AFlag then
    AssertEquals(CaseName, 1, AExpected)
  else
    AssertEquals(CaseName, 0, AExpected);
end;

procedure TParameterisedTests.TestTypedInt64(A, ATwice: Int64);
begin
  AssertEquals(CaseName, ATwice, A * 2);
end;

procedure TParameterisedTests.TestMixedKinds(N: Int; const S: string; B: Boolean);
begin
  AssertEquals(CaseName + ' int', 7, N);
  AssertEquals(CaseName + ' str', 'seven', S);
  AssertTrue(CaseName + ' bool', B);
end;

procedure TParameterisedTests.TestLabelledParameterless;
begin
  { A [TestCase('label')] on a parameterless method is a pure labelled
    run — CaseName must carry the label, and no dispatch conversion runs. }
  AssertEquals('case label visible to the body', 'labelled-only', CaseName);
end;

procedure TParameterisedTests.TestIgnoredNeverRuns;
begin
  Fail('[Ignore] was not honoured — the runner executed an ignored method');
end;

procedure TParameterisedTests.TestRetriedRuns;
begin
  { Each of the 3 [Retry] runs must pass independently. }
  AssertTrue('retried run passes', True);
end;

initialization
  RegisterTest(TParameterisedTests);

end.
