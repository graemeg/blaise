{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.

  Original work Copyright (c) the Free Pascal team — fpcunit.pp.
  Ported to Blaise by Graeme Geldenhuys, 2026.
}

{
  blaise.testing — minimum xUnit runtime surface for Blaise.

  Step 11d.  Direct port of the runtime surface of fpcunit.pp, scoped to the
  slice the 54 cp.test.*.pas regression units actually use.  The runner
  (text reporter) lives in a separate unit and is the subject of Step 11e.

  Departures from fpcunit:

    * No GUID on ITestListener — Blaise interfaces are GUID-free.
    * EAssertionFailed descends from TObject (not Exception) so that
      assertion failures are never accidentally caught by a user-level
      'on E: Exception do' handler inside a test method.
    * AssertRaises takes the EXPECTED CLASS AS A NAME STRING (compared
      against E.ClassName), not a 'class of Exception' reference compared
      with 'is' or InheritsFrom.  Blaise's 'is'/'as' operators require a
      static type name on the right (see uSemantic.AnalyseIsExpr) — they
      cannot test against a TClass VARIABLE — and TObject exposes no
      InheritsFrom/ClassType-returns-TClass builtin.  A generic method
      (e.g. 'AssertRaises<E: Exception>') would sidestep that, but generic
      methods are only proven on already-generic classes (Phase 10a,
      TList<T>.Map<R>); TAssert/TTestCase are plain classes, so that path
      is unverified.  The class-name-string comparison only depends on
      already-proven features (closures, E.ClassName, string equality).
    * Test enumeration of a registered class via 'class of TTestCase' is
      deferred to Step 11e (the runner).  v0 only stores the registered
      classes for the runner to walk later.
}

unit blaise.testing;

interface

uses
  Classes, Generics.Collections, SysUtils;

type
  { TRunMethod — type of a parameter-less method on any TObject descendant.
    Used as the cast target for the published-method dispatch trampoline:
    Code := MethodAddress(Self, FName); M.Code := Code; M.Data := Self;
    TRunMethod(M)(). }
  TRunMethod = procedure of object;

  { TCaseMethod — the [TestCase] typed-dispatch trampoline.  On x86-64
    SysV every dispatchable parameter kind (Integer-family ordinals,
    Int64, Boolean, string-as-data-pointer) travels in an integer-class
    register, and passing MORE register arguments than the callee reads is
    harmless — so one five-slot cast covers every supported signature.
    RunTest converts each [TestCase] token per the method's param-sig RTTI,
    places it in its slot, and calls through this type.  Consequences:
    at most 5 parameters, and no Double/Single params (those travel in
    xmm registers, which this trick cannot fill). }
  TCaseMethod = procedure(A1, A2, A3, A4, A5: UInt) of object;

  { TAssertProc — a parameterless closure passed to AssertRaises.  Real
    closures (capture, exceptions propagating through the call) landed with
    the anonymous-methods work; see AssertRaises for why the expected
    exception class is a name string rather than a TClass reference. }
  TAssertProc = reference to procedure;

  { TTestResult is declared first so TTest.Run can name it without the
    forward-class-declaration form that Blaise does not yet support. }
  TTestResult = class(TObject)
  private
    FNumberOfTests:    Integer;
    FNumberOfFailures: Integer;
    FNumberOfErrors:   Integer;
    FNumberOfIgnored:  Integer;
    FFailureList:      TList<String>;
    FErrorList:        TList<String>;
    FVerbose:          Boolean;
    FCurrentClassName: string;
    FCurrentTestName:  string;
  public
    constructor Create;

    procedure StartTest (AClassName, ATestName: string);
    procedure EndTest   (AOutcome: string);
    procedure AddFailure(AName, AMessage: string);
    procedure AddError  (AName, AMessage: string);
    procedure AddIgnored(AName, AMessage: string);
    procedure MergeFrom(ASource: TTestResult);

    function  Summary: string;

    property  NumberOfTests:    Integer read FNumberOfTests;
    property  NumberOfFailures: Integer read FNumberOfFailures;
    property  NumberOfErrors:   Integer read FNumberOfErrors;
    property  NumberOfIgnored:  Integer read FNumberOfIgnored;
    property  Failures:         TList<String> read FFailureList;
    property  Errors:           TList<String> read FErrorList;
    property  Verbose:          Boolean read FVerbose write FVerbose;
  end;

  { TTest — abstract root of the test hierarchy.  Concrete subclasses
    override Run and CountTestCases. }
  TTest = class(TObject)
  public
    procedure Run(AResult: TTestResult); virtual;
    function  CountTestCases: Integer; virtual;
  end;

  { TAssert — assertion helpers.  Implemented as instance methods rather
    than 'class procedure ... static' (Blaise does not yet parse 'class
    procedure').  Inside a published test method 'TFoo.TestX', a bare
    'AssertEquals(...)' call resolves through the inheritance chain to
    Self.AssertEquals, which is functionally equivalent. }
  TAssert = class(TTest)
  public
    procedure AssertTrue (AMsg: string; ACondition: Boolean); overload;
    procedure AssertTrue (ACondition: Boolean); overload;
    procedure AssertFalse(AMsg: string; ACondition: Boolean); overload;
    procedure AssertFalse(ACondition: Boolean); overload;

    procedure AssertEquals(AMsg: string; AExpected, AActual: Integer); overload;
    procedure AssertEquals(AExpected, AActual: Integer); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Int64); overload;
    procedure AssertEquals(AExpected, AActual: Int64); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: string); overload;
    procedure AssertEquals(AExpected, AActual: string); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Pointer); overload;
    procedure AssertEquals(AExpected, AActual: Pointer); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Boolean); overload;
    procedure AssertEquals(AExpected, AActual: Boolean); overload;
    { Floats compare within a tolerance, as FPCUnit's
      AssertEquals(Expected, Actual, Delta): the assertion holds when the two
      are equal or differ by at most ADelta.  A NaN on either side fails (a
      plain Abs(E - A) > Delta test lets it through), and an infinity
      matches only itself.  Single arguments widen to Double. }
    procedure AssertEquals(AMsg: string; AExpected, AActual, ADelta: Float64); overload;
    procedure AssertEquals(AExpected, AActual, ADelta: Float64); overload;

    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Integer); overload;
    procedure AssertNotEquals(AExpected, AActual: Integer); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Int64); overload;
    procedure AssertNotEquals(AExpected, AActual: Int64); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: string); overload;
    procedure AssertNotEquals(AExpected, AActual: string); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Boolean); overload;
    procedure AssertNotEquals(AExpected, AActual: Boolean); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Pointer); overload;
    procedure AssertNotEquals(AExpected, AActual: Pointer); overload;

    procedure AssertNotNull(AMsg: string; AObject: TObject); overload;
    procedure AssertNotNull(AObject: TObject); overload;
    procedure AssertNull   (AMsg: string; AObject: TObject); overload;
    procedure AssertNull   (AObject: TObject); overload;
    { AssertNotNil — verifies that a Pointer value is not nil.
      Use for type descriptors, raw pointers, and other non-TObject values. }
    procedure AssertNotNil(AMsg: string; APtr: Pointer); overload;
    procedure AssertNotNil(APtr: Pointer); overload;
    procedure AssertSame   (AMsg: string; AExpected, AActual: TObject); overload;
    procedure AssertSame   (AExpected, AActual: TObject); overload;

    { AssertContains — verifies that AHaystack contains ASubstring.
      Failure message quotes both the needle and haystack, which is far
      more useful than 'AssertTrue failed' when a Pos() check fails. }
    procedure AssertContains(AMsg: string; const ASubstring, AHaystack: string); overload;
    procedure AssertContains(const ASubstring, AHaystack: string); overload;

    { AssertRaises — runs AProc and verifies it raises an exception whose
      ClassName is AExpectedClassName (see the unit header for why this is
      a name string, not a TClass).  Fails if no exception is raised, or if
      a DIFFERENT exception class is raised (the failure message reports
      what was actually thrown, rather than swallowing it silently). }
    procedure AssertRaises(AMsg, AExpectedClassName: string; AProc: TAssertProc); overload;
    procedure AssertRaises(AExpectedClassName: string; AProc: TAssertProc); overload;

    { AssertNotRaises — runs AProc and fails if it raises ANY exception (the
      failure message reports the class and message of whatever was
      thrown). The complement of AssertRaises: useful for regression tests
      pinning down "this used to throw, assert it no longer does". }
    procedure AssertNotRaises(AMsg: string; AProc: TAssertProc); overload;
    procedure AssertNotRaises(AProc: TAssertProc); overload;

    procedure Fail(AMsg: string);
    procedure Ignore(AMsg: string);
  end;

  { TTestCase — base class for fixtures.  Each fixture class declares its
    test methods inside a 'published' visibility section; the hot path
    in RunTest looks them up via MethodAddress and dispatches via a
    procedure-of-object cast. }
  TTestCase = class(TAssert)
  private
    FName:      string;
    FClassName: string;
    FCaseName:  string;   { [TestCase] label; '' = plain run }
    FCaseArgs:  string;   { [TestCase] raw comma-separated argument list }
    FCaseSig:   string;   { published-method param-sig ('' = parameterless);
                            drives RunTest's typed dispatch }
  protected
    procedure SetUp;    virtual;
    procedure TearDown; virtual;
  public
    constructor Create(AName: string);
    procedure   SetClassName(AClassName: string);
    { Attach one [TestCase]'s data before Run: the case label, its raw
      argument list, and the method's param-kind signature. }
    procedure   SetCase(ACaseName, ACaseArgs, ACaseSig: string);
    { 'TestAdd[simple]' for a parameterised run, else the method name. }
    function    DisplayName: string;
    procedure   RunTest;            virtual;
    procedure   Run(AResult: TTestResult); override;
    function    CountTestCases: Integer; override;
    property    TestName:  string read FName;
    property    ClassName: string read FClassName;
    property    CaseName:  string read FCaseName;
  end;

  { TTestCaseClass — class-of reference used by RegisterTest. }
  TTestCaseClass = class of TTestCase;

  { ThreadedAttribute — apply [Threaded] to a TTestCase subclass to signal
    the test runner to execute that suite in a dedicated subprocess, enabling
    parallel execution of independent test suites. }
  ThreadedAttribute = class(TCustomAttribute)
  end;

  { TestCaseAttribute — one parameterised run of a published test method:

        [TestCase('simple',   '2,2,4')]
        [TestCase('negative', '-1,1,0')]
        procedure TestAdd(A, B, Expected: Integer);

    Args is a comma-separated value list converted to the method's declared
    parameter types by the runner (via the published-method param-sig RTTI)
    and passed as real arguments.  Supported parameter types: Integer-family
    ordinals, Int64, Boolean, string (no commas inside string values).
    Each case runs as its own test, reported as 'TestAdd[simple]'.  On a
    parameterless method the attribute is a pure labelled run. }
  TestCaseAttribute = class(TCustomAttribute)
  private
    FName: string;
    FArgs: string;
  public
    constructor Create(AName: string); overload;
    constructor Create(AName, AArgs: string); overload;
    property Name: string read FName;
    property Args: string read FArgs;
  end;

  { IgnoreAttribute — [Ignore('reason')] skips the method entirely; the
    runner records it as ignored with the reason, without executing it. }
  IgnoreAttribute = class(TCustomAttribute)
  private
    FReason: string;
  public
    constructor Create(AReason: string);
    property Reason: string read FReason;
  end;

  { CategoryAttribute — [Category('slow')] on a method or a suite class.
    The runner's --exclude-category flag skips matching tests. }
  CategoryAttribute = class(TCustomAttribute)
  private
    FName: string;
  public
    constructor Create(AName: string);
    property Name: string read FName;
  end;

  { RetryAttribute — [Retry(3)] runs the method (or each of its
    [TestCase]s) N times; useful for flushing out flaky tests.
    (Named Retry rather than Repeat: 'repeat' is a reserved word.) }
  RetryAttribute = class(TCustomAttribute)
  private
    FCount: Integer;
  public
    constructor Create(ACount: Integer);
    property Count: Integer read FCount;
  end;

  { EAssertionFailed — raised by Fail / Assert* on failure.  Descends
    from TObject (not Exception) to keep this unit standalone. }
  EAssertionFailed = class(TObject)
  private
    FMessage: string;
  public
    constructor Create(AMessage: string);
    function    ToString: string; override;
    property    Message: string read FMessage;
  end;

  { EIgnoredTest — raised by Ignore() to signal the runner to skip the
    test and record it as ignored rather than failed or errored. }
  EIgnoredTest = class(TObject)
  private
    FMessage: string;
  public
    constructor Create(AMessage: string);
    property    Message: string read FMessage;
  end;

{ Global test registry.  RegisterTest stores classes; the runner (Step
  11e) iterates over them, walks each class's published-method table to
  build per-method TTestCase instances, and runs each one. }
procedure RegisterTest(ATestClass: TTestCaseClass);
function  GetRegisteredTestCount: Integer;
function  GetRegisteredTest(AIndex: Integer): TTestCaseClass;

implementation

{ -----------------------------------------------------------------------
  Global registry storage
  ----------------------------------------------------------------------- }

var
  GTestRegistry: TList<TTestCaseClass>;  { registered test-case classes }

{ -----------------------------------------------------------------------
  TTest
  ----------------------------------------------------------------------- }

procedure TTest.Run(AResult: TTestResult);
begin
  { Abstract in spirit; concrete subclasses override. }
end;

function TTest.CountTestCases: Integer;
begin
  Result := 1;
end;

{ -----------------------------------------------------------------------
  TAssert
  ----------------------------------------------------------------------- }

procedure TAssert.AssertTrue(AMsg: string; ACondition: Boolean);
begin
  if not ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertTrue(ACondition: Boolean);
begin
  if not ACondition then
    Self.Fail('AssertTrue failed');
end;

procedure TAssert.AssertFalse(AMsg: string; ACondition: Boolean);
begin
  if ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertFalse(ACondition: Boolean);
begin
  if ACondition then
    Self.Fail('AssertFalse failed');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Integer);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + IntToStr(AExpected)
                   + '  Actual: '  + IntToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: Integer);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: ' + IntToStr(AExpected)
              + '  Actual: '  + IntToStr(AActual));
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Int64);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + Int64ToStr(AExpected)
                   + '  Actual: '  + Int64ToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: Int64);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: ' + Int64ToStr(AExpected)
              + '  Actual: '  + Int64ToStr(AActual));
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual,
  ADelta: Float64);
begin
  if AExpected = AActual then
    Exit;
  if not (Abs(AExpected - AActual) <= ADelta) then
    Self.Fail(AMsg + ' Expected: ' + DoubleToStr(AExpected) + '  Actual: ' +
      DoubleToStr(AActual) + '  Delta: ' + DoubleToStr(ADelta));
end;

procedure TAssert.AssertEquals(AExpected, AActual, ADelta: Float64);
begin
  Self.AssertEquals('', AExpected, AActual, ADelta);
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: "' + AExpected + '"  Actual: "' + AActual + '"');
end;

procedure TAssert.AssertEquals(AExpected, AActual: string);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: "' + AExpected + '"  Actual: "' + AActual + '"');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Pointer);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected and actual pointers differ');
end;

procedure TAssert.AssertEquals(AExpected, AActual: Pointer);
begin
  if AExpected <> AActual then
    Self.Fail('Expected and actual pointers differ');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Boolean);
var
  ExpStr, ActStr: string;
begin
  if AExpected <> AActual then
  begin
    if AExpected then ExpStr := 'True' else ExpStr := 'False';
    if AActual   then ActStr := 'True' else ActStr := 'False';
    Self.Fail(AMsg + ' Expected: ' + ExpStr + '  Actual: ' + ActStr);
  end;
end;

procedure TAssert.AssertEquals(AExpected, AActual: Boolean);
var
  ExpStr, ActStr: string;
begin
  if AExpected <> AActual then
  begin
    if AExpected then ExpStr := 'True' else ExpStr := 'False';
    if AActual   then ActStr := 'True' else ActStr := 'False';
    Self.Fail('Expected: ' + ExpStr + '  Actual: ' + ActStr);
  end;
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Integer);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + IntToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Integer);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: ' + IntToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Int64);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + Int64ToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Int64);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: ' + Int64ToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: string);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: "' + AActual + '"');
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: string);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: "' + AActual + '"');
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Boolean);
var S: string;
begin
  if AExpected = AActual then
  begin
    if AActual then S := 'True' else S := 'False';
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + S);
  end;
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Boolean);
var S: string;
begin
  if AExpected = AActual then
  begin
    if AActual then S := 'True' else S := 'False';
    Self.Fail('Expected values to differ, both are: ' + S);
  end;
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Pointer);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected pointers to differ');
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Pointer);
begin
  if AExpected = AActual then
    Self.Fail('Expected pointers to differ');
end;

procedure TAssert.AssertContains(AMsg: string; const ASubstring, AHaystack: string);
begin
  if Pos(ASubstring, AHaystack) < 0 then
    Self.Fail(AMsg + ' Expected "' + ASubstring + '" to appear in: "' + AHaystack + '"');
end;

procedure TAssert.AssertContains(const ASubstring, AHaystack: string);
begin
  if Pos(ASubstring, AHaystack) < 0 then
    Self.Fail('Expected "' + ASubstring + '" to appear in: "' + AHaystack + '"');
end;

procedure TAssert.AssertRaises(AMsg, AExpectedClassName: string; AProc: TAssertProc);
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AProc()
  except
    on E: Exception do
    begin
      if E.ClassName = AExpectedClassName then
        Raised := True
      else
        Self.Fail(AMsg + ' expected ' + AExpectedClassName + ' but got ' +
                  E.ClassName + ': ' + E.Message);
    end;
  end;
  if not Raised then
    Self.Fail(AMsg + ' expected ' + AExpectedClassName +
              ' to be raised, but no exception was');
end;

procedure TAssert.AssertRaises(AExpectedClassName: string; AProc: TAssertProc);
begin
  Self.AssertRaises('', AExpectedClassName, AProc);
end;

procedure TAssert.AssertNotRaises(AMsg: string; AProc: TAssertProc);
begin
  try
    AProc()
  except
    on E: Exception do
      Self.Fail(AMsg + ' expected no exception, but got ' +
                E.ClassName + ': ' + E.Message);
  end;
end;

procedure TAssert.AssertNotRaises(AProc: TAssertProc);
begin
  Self.AssertNotRaises('', AProc);
end;

procedure TAssert.AssertNotNull(AMsg: string; AObject: TObject);
begin
  if AObject = nil then
    Self.Fail(AMsg + ' Expected non-nil object');
end;

procedure TAssert.AssertNotNull(AObject: TObject);
begin
  if AObject = nil then
    Self.Fail('Expected non-nil object');
end;

procedure TAssert.AssertNull(AMsg: string; AObject: TObject);
begin
  if AObject <> nil then
    Self.Fail(AMsg + ' Expected nil object');
end;

procedure TAssert.AssertNull(AObject: TObject);
begin
  if AObject <> nil then
    Self.Fail('Expected nil object');
end;

procedure TAssert.AssertNotNil(AMsg: string; APtr: Pointer);
begin
  if APtr = nil then
    Self.Fail(AMsg + ' Expected non-nil pointer');
end;

procedure TAssert.AssertNotNil(APtr: Pointer);
begin
  if APtr = nil then
    Self.Fail('Expected non-nil pointer');
end;

procedure TAssert.AssertSame(AMsg: string; AExpected, AActual: TObject);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected the same object instance');
end;

procedure TAssert.AssertSame(AExpected, AActual: TObject);
begin
  if AExpected <> AActual then
    Self.Fail('Expected the same object instance');
end;

procedure TAssert.Fail(AMsg: string);
begin
  raise EAssertionFailed.Create(AMsg);
end;

procedure TAssert.Ignore(AMsg: string);
begin
  raise EIgnoredTest.Create(AMsg);
end;

{ -----------------------------------------------------------------------
  Attribute classes
  ----------------------------------------------------------------------- }

constructor TestCaseAttribute.Create(AName: string);
begin
  inherited Create();
  Self.FName := AName;
  Self.FArgs := '';
end;

constructor TestCaseAttribute.Create(AName, AArgs: string);
begin
  inherited Create();
  Self.FName := AName;
  Self.FArgs := AArgs;
end;

constructor IgnoreAttribute.Create(AReason: string);
begin
  inherited Create();
  Self.FReason := AReason;
end;

constructor CategoryAttribute.Create(AName: string);
begin
  inherited Create();
  Self.FName := AName;
end;

constructor RetryAttribute.Create(ACount: Integer);
begin
  inherited Create();
  Self.FCount := ACount;
end;

{ -----------------------------------------------------------------------
  [TestCase] argument-list helpers — plain comma split with ASCII-space
  trimming.  No quoting: a string argument must not contain a comma.
  ----------------------------------------------------------------------- }

function CaseArgCount(const AArgs: string): Integer;
var
  I: Integer;
begin
  if Length(AArgs) = 0 then Exit(0);
  Result := 1;
  for I := 0 to Length(AArgs) - 1 do
    if AArgs[I] = ',' then
      Result := Result + 1;
end;

function CaseArgAt(const AArgs: string; AIndex: Integer): string;
var
  I, Start, Seen: Integer;
  Lo, Hi:         Integer;
begin
  Result := '';
  Start  := 0;
  Seen   := 0;
  for I := 0 to Length(AArgs) do
  begin
    if (I = Length(AArgs)) or (AArgs[I] = ',') then
    begin
      if Seen = AIndex then
      begin
        { Trim leading/trailing spaces from AArgs[Start..I-1]. }
        Lo := Start;
        Hi := I - 1;
        while (Lo <= Hi) and (AArgs[Lo] = ' ') do Lo := Lo + 1;
        while (Hi >= Lo) and (AArgs[Hi] = ' ') do Hi := Hi - 1;
        Exit(Copy(AArgs, Lo, Hi - Lo + 1));
      end;
      Seen  := Seen + 1;
      Start := I + 1;
    end;
  end;
end;

{ -----------------------------------------------------------------------
  TTestCase
  ----------------------------------------------------------------------- }

constructor TTestCase.Create(AName: string);
begin
  inherited Create();
  Self.FName      := AName;
  Self.FClassName := '';
  Self.FCaseName  := '';
  Self.FCaseArgs  := '';
  Self.FCaseSig   := '';
end;

procedure TTestCase.SetClassName(AClassName: string);
begin
  Self.FClassName := AClassName;
end;

procedure TTestCase.SetCase(ACaseName, ACaseArgs, ACaseSig: string);
begin
  Self.FCaseName := ACaseName;
  Self.FCaseArgs := ACaseArgs;
  Self.FCaseSig  := ACaseSig;
end;

function TTestCase.DisplayName: string;
begin
  if Self.FCaseName <> '' then
    Result := Self.FName + '[' + Self.FCaseName + ']'
  else
    Result := Self.FName;
end;

procedure TTestCase.SetUp;
begin
end;

procedure TTestCase.TearDown;
begin
end;

function TTestCase.CountTestCases: Integer;
begin
  Result := 1;
end;

{ Hot path: dispatch via published-method address.  This is the line
  that motivated Steps 11a/b/c.

  Parameterised dispatch ([TestCase]): when FCaseSig is non-empty the
  method declares parameters; each comma-separated token of FCaseArgs is
  converted per its sig code and placed in an integer-register slot, then
  the method is invoked through the five-slot TCaseMethod trampoline (see
  its declaration for the ABI argument).  String tokens are kept alive in
  Toks[] across the call — the slot holds only the data pointer. }
procedure TTestCase.RunTest;
var
  M:       TMethod;
  Code:    Pointer;
  Run:     TRunMethod;
  CaseRun: TCaseMethod;
  Slots:   array[0..4] of UInt;
  Toks:    array[0..4] of string;
  N, I:    Integer;
begin
  Code := MethodAddress(Self, Self.FName);
  if Code = nil then
    Self.Fail('Method ' + Self.FName + ' not found in published section');
  M.Code := Code;
  M.Data := Self;
  if Self.FCaseSig = '' then
  begin
    Run := TRunMethod(M);
    Run();
    Exit;
  end;
  N := Length(Self.FCaseSig);
  if N > 5 then
    Self.Fail('[TestCase] dispatch supports at most 5 parameters, method ''' +
      Self.FName + ''' declares ' + IntToStr(N));
  if CaseArgCount(Self.FCaseArgs) <> N then
    Self.Fail('[TestCase(''' + Self.FCaseName + ''')] supplies ' +
      IntToStr(CaseArgCount(Self.FCaseArgs)) + ' argument(s) but method ''' +
      Self.FName + ''' declares ' + IntToStr(N) + ' parameter(s)');
  for I := 0 to 4 do
    Slots[I] := 0;
  for I := 0 to N - 1 do
  begin
    Toks[I] := CaseArgAt(Self.FCaseArgs, I);
    if Self.FCaseSig[I] = 'i' then
      Slots[I] := UInt(StrToInt(Toks[I]))
    else if Self.FCaseSig[I] = 'I' then
      Slots[I] := UInt(StrToInt64(Toks[I]))
    else if Self.FCaseSig[I] = 'b' then
    begin
      if SameText(Toks[I], 'True') or (Toks[I] = '1') then
        Slots[I] := 1
      else
        Slots[I] := 0;
    end
    else if Self.FCaseSig[I] = 's' then
      Slots[I] := UInt(PChar(Toks[I]))
    else
      Self.Fail('[TestCase] cannot dispatch parameter ' + IntToStr(I) +
        ' of method ''' + Self.FName + ''' (kind ''' +
        Copy(Self.FCaseSig, I, 1) +
        '''): only Integer-family, Int64, Boolean and string are supported');
  end;
  CaseRun := TCaseMethod(M);
  CaseRun(Slots[0], Slots[1], Slots[2], Slots[3], Slots[4]);
end;

procedure TTestCase.Run(AResult: TTestResult);
var
  Outcome: string;
begin
  { DisplayName carries the [TestCase] label ('TestAdd[simple]') so each
    parameterised case reports as its own test. }
  AResult.StartTest(Self.FClassName, Self.DisplayName());
  Outcome := 'OK';
  try
    try
      { SetUp sits INSIDE the exception-mapping block: a SetUp failure
        is this test's ERROR (JUnit semantics), never a runner abort.
        The body is skipped when SetUp raises; TearDown still runs. }
      try
        Self.SetUp();
        Self.RunTest();
      except
        on E: EAssertionFailed do
        begin
          Outcome := 'FAIL';
          AResult.AddFailure(Self.DisplayName(), E.ToString());
        end;
        on E: EIgnoredTest do
        begin
          Outcome := 'IGNORED';
          AResult.AddIgnored(Self.DisplayName(), E.FMessage);
        end;
        on E: Exception do
        begin
          Outcome := 'ERROR';
          AResult.AddError(Self.DisplayName(), E.ClassName + ': ' + E.Message);
        end;
        on E: TObject do
        begin
          Outcome := 'ERROR';
          AResult.AddError(Self.DisplayName(), 'Unhandled exception: ' + E.ClassName);
        end;
      end;
    finally
      { A TearDown failure must not abort the runner either; it marks
        the test as an ERROR unless a worse outcome is already set. }
      try
        Self.TearDown();
      except
        on E: Exception do
          if Outcome = 'OK' then
          begin
            Outcome := 'ERROR';
            AResult.AddError(Self.DisplayName(),
              'TearDown: ' + E.ClassName + ': ' + E.Message);
          end;
        on E: TObject do
          if Outcome = 'OK' then
          begin
            Outcome := 'ERROR';
            AResult.AddError(Self.DisplayName(),
              'TearDown: unhandled exception: ' + E.ClassName);
          end;
      end;
    end;
  finally
    AResult.EndTest(Outcome);
  end;
end;

{ -----------------------------------------------------------------------
  TTestResult
  ----------------------------------------------------------------------- }

constructor TTestResult.Create;
begin
  inherited Create();
  Self.FNumberOfTests    := 0;
  Self.FNumberOfFailures := 0;
  Self.FNumberOfErrors   := 0;
  Self.FNumberOfIgnored  := 0;
  Self.FFailureList      := TList<String>.Create();
  Self.FErrorList        := TList<String>.Create();
  Self.FVerbose          := False;
  Self.FCurrentClassName := '';
  Self.FCurrentTestName  := '';
end;

procedure TTestResult.StartTest(AClassName, ATestName: string);
begin
  Self.FNumberOfTests    := Self.FNumberOfTests + 1;
  Self.FCurrentClassName := AClassName;
  Self.FCurrentTestName  := ATestName;
  if Self.FVerbose then
    Write(AClassName + '.' + ATestName + ' ... ');
end;

procedure TTestResult.EndTest(AOutcome: string);
begin
  if Self.FVerbose then
    WriteLn(AOutcome);
end;

procedure TTestResult.AddFailure(AName, AMessage: string);
begin
  Self.FNumberOfFailures := Self.FNumberOfFailures + 1;
  Self.FFailureList.Add(AName + ': ' + AMessage);
end;

procedure TTestResult.AddError(AName, AMessage: string);
begin
  Self.FNumberOfErrors := Self.FNumberOfErrors + 1;
  Self.FErrorList.Add(AName + ': ' + AMessage);
end;

procedure TTestResult.AddIgnored(AName, AMessage: string);
begin
  Self.FNumberOfIgnored := Self.FNumberOfIgnored + 1;
end;

procedure TTestResult.MergeFrom(ASource: TTestResult);
var I: Integer;
begin
  Self.FNumberOfTests    := Self.FNumberOfTests    + ASource.FNumberOfTests;
  Self.FNumberOfFailures := Self.FNumberOfFailures + ASource.FNumberOfFailures;
  Self.FNumberOfErrors   := Self.FNumberOfErrors   + ASource.FNumberOfErrors;
  Self.FNumberOfIgnored  := Self.FNumberOfIgnored  + ASource.FNumberOfIgnored;
  for I := 0 to ASource.FFailureList.Count - 1 do
    Self.FFailureList.Add(ASource.FFailureList.Get(I));
  for I := 0 to ASource.FErrorList.Count - 1 do
    Self.FErrorList.Add(ASource.FErrorList.Get(I));
end;

function TTestResult.Summary: string;
begin
  if (Self.FNumberOfFailures = 0) and (Self.FNumberOfErrors = 0) then
  begin
    Result := 'OK (' + IntToStr(Self.FNumberOfTests) + ' tests';
    if Self.FNumberOfIgnored > 0 then
      Result := Result + ', ' + IntToStr(Self.FNumberOfIgnored) + ' ignored';
    Result := Result + ')';
  end
  else
    Result := 'FAIL (' + IntToStr(Self.FNumberOfTests)    + ' tests, '
                       + IntToStr(Self.FNumberOfFailures) + ' failures, '
                       + IntToStr(Self.FNumberOfErrors)   + ' errors)';
end;

{ -----------------------------------------------------------------------
  EAssertionFailed
  ----------------------------------------------------------------------- }

constructor EAssertionFailed.Create(AMessage: string);
begin
  inherited Create();
  Self.FMessage := AMessage;
end;

function EAssertionFailed.ToString: string;
begin
  Result := Self.FMessage;
end;

constructor EIgnoredTest.Create(AMessage: string);
begin
  inherited Create();
  Self.FMessage := AMessage;
end;

{ -----------------------------------------------------------------------
  Global registry
  ----------------------------------------------------------------------- }

procedure RegisterTest(ATestClass: TTestCaseClass);
begin
  if GTestRegistry = nil then
    GTestRegistry := TList<TTestCaseClass>.Create();
  GTestRegistry.Add(ATestClass);
end;

function GetRegisteredTestCount: Integer;
begin
  if GTestRegistry = nil then
    Result := 0
  else
    Result := GTestRegistry.Count;
end;

function GetRegisteredTest(AIndex: Integer): TTestCaseClass;
begin
  Result := GTestRegistry.Get(AIndex);
end;

end.
