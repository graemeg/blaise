{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.runner_filters;

{ Unit tests for the suite-filter helpers in blaise.testing.runner.text.
  Exercises the pure-function parts (SplitSuiteSpec, AppendSuiteFilter,
  MatchesFilters) so the CLI surface — multiple --suite flags and
  comma-delimited values — has direct regression coverage. }

interface

uses
  blaise.testing, Generics.Collections,
  blaise.testing.runner.text;

type
  TRunnerFiltersTests = class(TTestCase)
  published
    procedure TestSplit_ClassOnly;
    procedure TestSplit_ClassAndMethod;
    procedure TestSplit_EmptyMethod;

    procedure TestAppend_Single;
    procedure TestAppend_CommaSeparated;
    procedure TestAppend_TrimsSpaces;
    procedure TestAppend_SkipsEmptyEntries;

    procedure TestMatches_EmptyFiltersAcceptAll;
    procedure TestMatches_ClassFilterMatchesAnyMethod;
    procedure TestMatches_ClassFilterRejectsOtherClass;
    procedure TestMatches_MethodFilterIsExact;
    procedure TestMatches_MethodFilterRejectsOtherMethod;
    procedure TestMatches_MultipleFiltersAreUnion;

    procedure TestParseSub_SingleLineFailures;
    procedure TestParseSub_MultiLineFailureKeepsLaterOnes;
    procedure TestParseSub_ContinuationNotCountedAsTest;
    procedure TestParseSub_FailuresThenErrors;
  end;

implementation

procedure TRunnerFiltersTests.TestSplit_ClassOnly;
var S, M: string;
begin
  SplitSuiteSpec('TFooTests', S, M);
  AssertEquals('class part',  'TFooTests', S);
  AssertEquals('method part', '',          M);
end;

procedure TRunnerFiltersTests.TestSplit_ClassAndMethod;
var S, M: string;
begin
  SplitSuiteSpec('TFooTests.TestBar', S, M);
  AssertEquals('class part',  'TFooTests', S);
  AssertEquals('method part', 'TestBar',   M);
end;

procedure TRunnerFiltersTests.TestSplit_EmptyMethod;
var S, M: string;
begin
  SplitSuiteSpec('TFooTests.', S, M);
  AssertEquals('class part',  'TFooTests', S);
  AssertEquals('method part', '',          M);
end;

procedure TRunnerFiltersTests.TestAppend_Single;
var L: TList<String>;
begin
  L := TList<String>.Create();
  AppendSuiteFilter(L, 'TFoo');
  AssertEquals('count', 1, L.Count);
  AssertEquals('value', 'TFoo', L.Get(0));
end;

procedure TRunnerFiltersTests.TestAppend_CommaSeparated;
var L: TList<String>;
begin
  L := TList<String>.Create();
  AppendSuiteFilter(L, 'TA,TB.m,TC');
  AssertEquals('count',  3, L.Count);
  AssertEquals('first',  'TA',   L.Get(0));
  AssertEquals('second', 'TB.m', L.Get(1));
  AssertEquals('third',  'TC',   L.Get(2));
end;

procedure TRunnerFiltersTests.TestAppend_TrimsSpaces;
var L: TList<String>;
begin
  L := TList<String>.Create();
  AppendSuiteFilter(L, '  TA , TB.m ');
  AssertEquals('count',  2, L.Count);
  AssertEquals('first',  'TA',   L.Get(0));
  AssertEquals('second', 'TB.m', L.Get(1));
end;

procedure TRunnerFiltersTests.TestAppend_SkipsEmptyEntries;
var L: TList<String>;
begin
  L := TList<String>.Create();
  AppendSuiteFilter(L, ',TA,,TB,');
  AssertEquals('count',  2, L.Count);
  AssertEquals('first',  'TA', L.Get(0));
  AssertEquals('second', 'TB', L.Get(1));
end;

procedure TRunnerFiltersTests.TestMatches_EmptyFiltersAcceptAll;
var L: TList<String>;
begin
  L := TList<String>.Create();
  AssertTrue('empty list matches arbitrary test',
    MatchesFilters(L, 'TFoo', 'TestBar'));
  AssertTrue('nil filter list matches arbitrary test',
    MatchesFilters(nil, 'TFoo', 'TestBar'));
end;

procedure TRunnerFiltersTests.TestMatches_ClassFilterMatchesAnyMethod;
var L: TList<String>;
begin
  L := TList<String>.Create();
  L.Add('TFoo');
  AssertTrue('first method',  MatchesFilters(L, 'TFoo', 'TestA'));
  AssertTrue('second method', MatchesFilters(L, 'TFoo', 'TestB'));
end;

procedure TRunnerFiltersTests.TestMatches_ClassFilterRejectsOtherClass;
var L: TList<String>;
begin
  L := TList<String>.Create();
  L.Add('TFoo');
  AssertFalse('other class', MatchesFilters(L, 'TBar', 'TestA'));
end;

procedure TRunnerFiltersTests.TestMatches_MethodFilterIsExact;
var L: TList<String>;
begin
  L := TList<String>.Create();
  L.Add('TFoo.TestBar');
  AssertTrue('exact match', MatchesFilters(L, 'TFoo', 'TestBar'));
end;

procedure TRunnerFiltersTests.TestMatches_MethodFilterRejectsOtherMethod;
var L: TList<String>;
begin
  L := TList<String>.Create();
  L.Add('TFoo.TestBar');
  AssertFalse('different method same class',
    MatchesFilters(L, 'TFoo', 'TestQux'));
end;

procedure TRunnerFiltersTests.TestMatches_MultipleFiltersAreUnion;
var L: TList<String>;
begin
  L := TList<String>.Create();
  L.Add('TFoo.TestA');
  L.Add('TBar');
  AssertTrue('first filter hits',
    MatchesFilters(L, 'TFoo', 'TestA'));
  AssertTrue('second filter hits (class-only)',
    MatchesFilters(L, 'TBar', 'AnyMethod'));
  AssertFalse('neither hits',
    MatchesFilters(L, 'TFoo', 'TestZ'));
  AssertFalse('neither hits, other class',
    MatchesFilters(L, 'TBaz', 'TestA'));
end;

{ ---- ParseSubprocessOutput -------------------------------------------------
  A [Threaded] suite runs as a subprocess and its --verbose output is parsed
  back into the parent's result.  A failure message may span several lines (a
  compile failure carries the compiler's multi-line diagnostics).  The parser
  used to end the Failures section at the first unindented line, so every
  failure AFTER a multi-line one was dropped from the list AND the count --
  on macOS that hid 27 of 58 failing tests behind a smaller total. }

const
  LE = #10;

procedure TRunnerFiltersTests.TestParseSub_SingleLineFailures;
var R: TTestResult;
begin
  R := TTestResult.Create();
  ParseSubprocessOutput(
    'TS.TestA ... OK' + LE +
    'TS.TestB ... FAIL' + LE +
    'TS.TestC ... FAIL' + LE +
    'FAIL (3 tests, 2 failures, 0 errors)' + LE +
    'Failures:' + LE +
    '  TestB: expected 1' + LE +
    '  TestC: expected 2' + LE, R);
  AssertEquals('tests', 3, R.NumberOfTests);
  AssertEquals('failures', 2, R.NumberOfFailures);
  AssertEquals('listed', 2, R.Failures.Count);
end;

procedure TRunnerFiltersTests.TestParseSub_MultiLineFailureKeepsLaterOnes;
var R: TTestResult;
begin
  R := TTestResult.Create();
  ParseSubprocessOutput(
    'TS.TestA ... FAIL' + LE +
    'TS.TestB ... FAIL' + LE +
    'TS.TestC ... FAIL' + LE +
    'FAIL (3 tests, 3 failures, 0 errors)' + LE +
    'Failures:' + LE +
    '  TestA: compile failed: 2Code generation error: x' + LE +
    '' + LE +
    '  TestB: compile failed: line one' + LE +
    'line two of the same message' + LE +
    '  TestC: plain' + LE, R);
  AssertEquals('every failure counted', 3, R.NumberOfFailures);
  AssertEquals('every failure listed', 3, R.Failures.Count);
  AssertTrue('continuation kept with its failure',
    Pos('line two', R.Failures.Get(1)) >= 0);
  AssertTrue('last failure named', Pos('TestC: plain', R.Failures.Get(2)) = 0);
end;

procedure TRunnerFiltersTests.TestParseSub_ContinuationNotCountedAsTest;
var R: TTestResult;
begin
  R := TTestResult.Create();
  { a message line that happens to contain ' ... ' is message text, not a
    verbose outcome line, and must not inflate the test count }
  ParseSubprocessOutput(
    'TS.TestA ... FAIL' + LE +
    'FAIL (1 tests, 1 failures, 0 errors)' + LE +
    'Failures:' + LE +
    '  TestA: Expected "a ... b"' + LE +
    'Actual: "a ... c"' + LE, R);
  AssertEquals('tests', 1, R.NumberOfTests);
  AssertEquals('failures', 1, R.NumberOfFailures);
end;

procedure TRunnerFiltersTests.TestParseSub_FailuresThenErrors;
var R: TTestResult;
begin
  R := TTestResult.Create();
  ParseSubprocessOutput(
    'TS.TestA ... FAIL' + LE +
    'TS.TestB ... ERROR' + LE +
    'FAIL (2 tests, 1 failures, 1 errors)' + LE +
    'Failures:' + LE +
    '  TestA: multi' + LE +
    'line' + LE +
    'Errors:' + LE +
    '  TestB: EAccessViolation' + LE, R);
  AssertEquals('failures', 1, R.NumberOfFailures);
  AssertEquals('errors', 1, R.NumberOfErrors);
end;

initialization
  RegisterTest(TRunnerFiltersTests);

end.
