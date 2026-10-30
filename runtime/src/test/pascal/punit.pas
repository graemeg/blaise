{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: LGPL-2.1-or-later WITH FPC-exception
  Original work Copyright (c) 2014 by Michael Van Canneyt (Free Pascal project).
  Modified for the Blaise compiler by Graeme Geldenhuys, 2026.
}

{
  punit — minimal self-contained unit test framework for Blaise RTL tests.

  Designed for bootstrap testing where transitive RTL dependencies are a
  concern.  The implementation section has no uses clause beyond the system
  unit.  No RTTI, no TCustomApplication, no SysUtils, no IniFiles.

  Deviations from the FPC punit.pp (fcl-base/tests/punit.pp):

  Memory management:
    * New(P) / Dispose(P) / SetLength / Default(T) are not Blaise built-ins.
      All heap allocation uses GetMem / ReallocMem / FreeMem directly.
      Record initialisation uses ZeroMem.
    * 'array of T' is only a parameter type in Blaise (open array).
      TSuiteArray changed to PSuiteArray (raw pointer), TRunStartHandler
      signature changed to (Count: Integer; Suites: PSuiteArray).

  Types dropped entirely:
    * ShortString / AnsiString / UnicodeString / UTF8String → single 'string'
    * Currency overload dropped  (Blaise lacks Currency)
    * Double / Single / Extended / TDateTime — entirely absent; Blaise has no
      floating-point type support whatsoever.  The Double AssertEquals overload,
      DefaultDoubleDelta, DefaultSingleDelta, TTimeHook, and all time-hook
      functions have been removed.  GrowFactor is an Integer (150 = 1.5×, etc).
    * QWord → Int64  (Blaise lacks QWord)
    * Smallint / Shortint / Word / Longint → Integer (same QBE 'w' type)
    * TClass replaced with Pointer everywhere (no RTTI yet); pointer equality used

  Intrinsics replaced:
    * Str(X, S) → S := IntToStr(X)
    * FillChar(P^, N, 0) → ZeroMem(P, N)
    * Finalize(P^) → dropped (ARC manages string fields automatically)
    * Default(T) → ZeroMem on the memory block
    * Assert(expr) → runtime check with Halt(1)
    * Multi-arg Write/WriteLn → string concatenation

  Output:
    * File output (-o flag) is parsed but ignored; no Text file I/O in
      the early RTL.
    * GetSysTestOS always returns 'linux'.
    * SysGetSetting (INI-file reader) is absent.
}

unit punit;

interface

{ -----------------------------------------------------------------------
  Configuration variables
  ----------------------------------------------------------------------- }

var
  InitListLength   : Int;
  GrowFactor       : Int;
  DefaultSuiteName : string;
  RequirePassed    : Boolean;
  DefaultDoubleDelta : Float64;

{ -----------------------------------------------------------------------
  Core data types
  ----------------------------------------------------------------------- }

type
  TTestError = (
    teOK,
    teTestsRunning,
    teRegistryEmpty,
    teNoMemory,
    teNoSuite,
    teNoSuiteName,
    teSuiteSetupFailed,
    teSuiteTeardownFailed,
    teDuplicateSuite,
    teSuiteInactive,
    teNoTest,
    teNoTestName,
    teDuplicateTest,
    teTestNotInSuite,
    teTestInactive,
    teRunStartHandler,
    teRunCompleteHandler
  );

  TErrorAction = (
    eaIgnore,
    eaFail,
    eaAbort
  );

  { Bare procedural function types for tests and setup/teardown. }
  TTestSetup    = function : string;
  TTestTearDown = function : string;
  TTestRun      = function : string;
  TTestRunProc  = procedure;

  TTestOption  = (toInactive);
  TTestOptions = set of TTestOption;

  PTest = ^TTest;
  TTest = record
    Run     : TTestRun;
    RunProc : TTestRunProc;
    Name    : string;
    Options : TTestOptions;
    Data    : Pointer;
  end;

  PTestList = ^TTestList;
  { Manual growable array of PTest pointers. }
  TTestList = record
    Items    : Pointer;   { block of ^TTest values, each 8 bytes on 64-bit }
    Count    : Int;
    Capacity : Int;
  end;

  TSuiteOption  = (soInactive, soSetupTearDownPerTest);
  TSuiteOptions = set of TSuiteOption;

  PSuiteList = ^TSuiteList;
  { Manual growable array of ^TSuite pointers. }
  TSuiteList = record
    Items    : Pointer;   { block of ^TSuite values }
    Count    : Int;
    Capacity : Int;
  end;

  { Raw pointer block used for run-start hook.  Each slot is a PSuite (8 bytes).
    Callers build it with GetMem(Count * SizeOf(Pointer)) and free with FreeMem.
    Blaise does not yet support dynamic arrays with SetLength. }
  PSuiteArray = Pointer;

  PSuite = ^TSuite;
  TSuite = record
    Suites     : TSuiteList;
    Tests      : TTestList;
    Setup      : TTestSetup;
    Teardown   : TTestTearDown;
    Name       : string;
    Options    : TSuiteOptions;
    ParentSuite : ^TSuite;
    Data        : Pointer;
  end;

  TTestResult = (
    trEmpty,
    trOK,
    trSuiteInactive,
    trSuiteSetupFailed,
    trSuiteTearDownFailed,
    trTestInactive,
    trTestIgnore,
    trAssertFailed,
    trTestError,
    trHandlerError
  );

  PResultRecord = ^TResultRecord;
  TResultRecord = record
    Suite           : ^TSuite;
    Test            : ^TTest;
    ElapsedTime     : Int;
    TestResult      : TTestResult;
    TestMessage     : string;
    ExpectException : Pointer;
    ParentResult,
    ChildResults,
    NextResult      : ^TResultRecord;
  end;

  TSuiteStats = record
    Suites,
    TestsFailed,
    TestsInactive,
    TestsIgnored,
    TestsRun,
    TestsError,
    TestsUnimplemented : Int;
  end;

  PRunSummary = ^TRunSummary;
  TRunSummary = record
    SuitesRun          : Int;
    SuitesFailed       : Int;
    SuitesInactive     : Int;
    TestsRun           : Int;
    TestsFailed        : Int;
    TestsIgnored       : Int;
    TestsUnimplemented : Int;
    TestsInactive      : Int;
    AssertCount        : Int;
    Results            : TResultRecord;
    ElapsedTime        : Int;
  end;

  EFail = class(TObject)
  private
    FMessage : string;
  public
    constructor Create(const AMessage : string);
    function ToString : string; virtual;
  end;

  EIgnore = class(EFail);

{ -----------------------------------------------------------------------
  Test registry management
  ----------------------------------------------------------------------- }

function  SetupTestRegistry : TTestError;
function  TearDownTestRegistry : TTestError;
function  TestRegistryOK : Boolean;

{ -----------------------------------------------------------------------
  Suite management
  ----------------------------------------------------------------------- }

function AddSuite(const AName : string; ASetup : TTestSetup;
  ATearDown : TTestTearDown; AParent : ^TSuite;
  aPerTestSetupTearDown : Boolean) : ^TSuite; overload;
function AddSuite(const AName : string; AParent : ^TSuite) : ^TSuite; overload;

function GetSuiteCount : Int; overload;
function GetSuiteCount(Recurse : Boolean) : Int; overload;
function GetSuiteCount(ASuite : ^TSuite) : Int; overload;
function GetSuiteCount(ASuite : ^TSuite; Recurse : Boolean) : Int; overload;
function GetSuiteIndex(const AName : string) : Int; overload;
function GetSuiteIndex(ASuite : ^TSuite; const AName : string) : Int; overload;
function GetSuite(const AIndex : Int) : ^TSuite; overload;
function GetSuite(const AName : string) : ^TSuite; overload;
function GetSuite(const AName : string; AParent : ^TSuite) : ^TSuite; overload;

{ -----------------------------------------------------------------------
  Test management
  ----------------------------------------------------------------------- }

function AddTest(const ATestName : string; ARun : TTestRun;
  const ASuiteName : string = '') : ^TTest; overload;
function AddTest(const ATestName : string; ARun : TTestRunProc;
  const ASuiteName : string = '') : ^TTest; overload;
function AddTest(const ATestName : string; ARun : TTestRun;
  const ASuite : ^TSuite) : ^TTest; overload;
function AddTest(const ATestName : string; ARun : TTestRunProc;
  const ASuite : ^TSuite) : ^TTest; overload;

function GetTestIndex(const ASuiteName : string; const ATestName : string) : Int; overload;
function GetTestIndex(const ASuite : ^TSuite; const ATestName : string) : Int; overload;
function GetTestIndex(const ASuite : ^TSuite; const ATest : ^TTest) : Int; overload;
function GetTestCount(const ASuiteName : string) : Int; overload;
function GetTestCount(const ASuite : ^TSuite) : Int; overload;
function GetTest(const ASuiteName : string; const ATestName : string) : ^TTest; overload;
function GetTest(const ASuite : ^TSuite; const ATestName : string) : ^TTest; overload;
function GetTest(const ASuite : ^TSuite; const ATestIndex : Int) : ^TTest; overload;
function TestIsInSuite(const ASuite : ^TSuite; const ATest : ^TTest) : Boolean;

{ -----------------------------------------------------------------------
  Running tests
  ----------------------------------------------------------------------- }

function  RunAllTests : TTestError;
function  RunSuite(const ASuiteName : string) : TTestError; overload;
function  RunSuite(ASuiteIndex : Int) : TTestError; overload;
function  RunSuite(ASuite : ^TSuite) : TTestError; overload;
function  RunTest(const ASuiteName : string; const ATestName : string) : TTestError; overload;
function  RunTest(ASuite : ^TSuite; const ATestName : string) : TTestError; overload;
function  RunTest(ASuite : ^TSuite; ATest : ^TTest) : TTestError; overload;
procedure RunTest(ARun : TTestRun); overload;

function  GetCurrentRun : TRunSummary;
function  GetCurrentSuite : ^TSuite;
function  GetCurrentTest : ^TTest;
function  GetCurrentResult : ^TResultRecord;
procedure GetSuiteStats(AResults : ^TResultRecord; out Stats : TSuiteStats);
function  CountResults(Results : ^TResultRecord) : Int;

{ -----------------------------------------------------------------------
  Assertions
  ----------------------------------------------------------------------- }

function Ignore(const Msg : string) : Boolean;
function Fail(const Msg : string) : Boolean;
function FailExit(const Msg : string) : Boolean;
function IgnoreExit(const Msg : string) : Boolean;
function AssertPassed : Boolean; overload;
function AssertPassed(AMessage : string) : Boolean; overload;

function AssertTrue(const AMessage : string; ACondition : Boolean) : Boolean;
function AssertFalse(const AMessage : string; ACondition : Boolean) : Boolean;

function AssertEquals(AMessage : string; const AExpected, AActual : string) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : Boolean) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : Byte) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : Int32) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : UInt32) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : Int64) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : UInt64) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual : Float64) : Boolean; overload;
function AssertEquals(AMessage : string; const AExpected, AActual, ADelta : Float64) : Boolean; overload;

function AssertNull(AMessage : string; const AValue : Pointer) : Boolean;
function AssertNotNull(AMessage : string; const AValue : Pointer) : Boolean;
function AssertEquals(AMessage : string; const AExpected, AActual : Pointer) : Boolean; overload;
function AssertDiffers(AMessage : string; const AExpected, AActual : Pointer) : Boolean;
function AssertSame(AMessage : string; const AExpected, AActual : TObject) : Boolean;
function AssertNotSame(AMessage : string; const AExpected, AActual : TObject) : Boolean;
function AssertInheritsFrom(AMessage : string; const AChild, AParent : TObject) : Boolean; overload;
function AssertInheritsFromClass(AMessage : string; const AChild, AParent : Pointer) : Boolean;
function AssertException(const AMessage : string; AExceptionClass : Pointer;
  ARun : TTestRun) : Boolean;
function ExpectException(AMessage : string; AClass : Pointer) : Boolean;

{ -----------------------------------------------------------------------
  Hooks
  ----------------------------------------------------------------------- }

type
  TRunStartHandler        = procedure(Count : Int; Suites : PSuiteArray);
  TRunCompleteHandler     = procedure(const ARunResult : TRunSummary);
  TSuiteStartHandler      = procedure(ASuite : ^TSuite);
  TSuiteCompleteHandler   = procedure(ASuite : ^TSuite;
    const SuiteResults : ^TResultRecord);
  TSuiteSetupFailureHandler    = procedure(ASuite : ^TSuite; const AError : string);
  TSuiteTearDownFailureHandler = procedure(ASuite : ^TSuite; const AError : string);
  TTestStartHandler       = procedure(ATest : ^TTest; ASuite : ^TSuite);
  TTestCompleteHandler    = procedure(ATest : ^TTest; ASuite : ^TSuite;
    const TestResult : ^TResultRecord);

function SetRunStartHandler(AHandler : TRunStartHandler) : TRunStartHandler;
function SetRunCompleteHandler(AHandler : TRunCompleteHandler) : TRunCompleteHandler;
function SetSuiteStartHandler(AHandler : TSuiteStartHandler) : TSuiteStartHandler;
function SetSuiteCompleteHandler(AHandler : TSuiteCompleteHandler) : TSuiteCompleteHandler;
function SetSuiteSetupFailureHandler(AHandler : TSuiteSetupFailureHandler) : TSuiteSetupFailureHandler;
function SetSuiteTearDownFailureHandler(AHandler : TSuiteTearDownFailureHandler) : TSuiteTearDownFailureHandler;
function SetTestStartHandler(AHandler : TTestStartHandler) : TTestStartHandler;
function SetTestCompleteHandler(AHandler : TTestCompleteHandler) : TTestCompleteHandler;

function GetSuiteStartHandler : TSuiteStartHandler;
function GetTestStartHandler : TTestStartHandler;
function GetTestCompleteHandler : TTestCompleteHandler;
function GetSuiteCompleteHandler : TSuiteCompleteHandler;
function GetRunStartHandler : TRunStartHandler;
function GetRunCompleteHandler : TRunCompleteHandler;
function GetSuiteSetupFailureHandler : TSuiteSetupFailureHandler;
function GetSuiteTearDownFailureHandler : TSuiteTearDownFailureHandler;
procedure ClearTestHooks;

{ -----------------------------------------------------------------------
  Error state
  ----------------------------------------------------------------------- }

function GetTestError : TTestError;
function GetTestErrorMessage : string;
function SetTestError(AError : TTestError) : TTestError;
function GetErrorAction : TErrorAction;
function SetErrorAction(AError : TErrorAction) : TErrorAction;

{ -----------------------------------------------------------------------
  System-level runner (hooks + CLI + RunAllSysTests)
  ----------------------------------------------------------------------- }

type
  TSysRunVerbosity = (rvQuiet, rvFailures, rvNormal, rvVerbose);

procedure SetupSysHandlers;
procedure TearDownSysHandlers;
function  GetSysRunVerbosity : TSysRunVerbosity;
function  SetSysRunVerbosity(AMode : TSysRunVerbosity) : TSysRunVerbosity;
procedure ProcessSysCommandline;
procedure RunAllSysTests;
function  GetSysTestOS : string;

implementation

{ -----------------------------------------------------------------------
  Module-level state
  ----------------------------------------------------------------------- }

var
  CurrentError       : TTestError;
  CurrentErrorAction : TErrorAction;

  TestRegistry : TSuiteList;

  GlobalSuiteStartHandler           : TSuiteStartHandler;
  GlobalTestStartHandler            : TTestStartHandler;
  GlobalTestCompleteHandler         : TTestCompleteHandler;
  GlobalSuiteCompleteHandler        : TSuiteCompleteHandler;
  GlobalRunStartHandler             : TRunStartHandler;
  GlobalRunCompleteHandler          : TRunCompleteHandler;
  GlobalSuiteSetupFailureHandler    : TSuiteSetupFailureHandler;
  GlobalSuiteTearDownFailureHandler : TSuiteTearDownFailureHandler;

  CurrentSuite       : ^TSuite;
  CurrentTest        : ^TTest;
  CurrentRun         : TRunSummary;
  CurrentSuiteResult,
  CurrentResult      : ^TResultRecord;

{ -----------------------------------------------------------------------
  EFail
  ----------------------------------------------------------------------- }

constructor EFail.Create(const AMessage : string);
begin
  FMessage := AMessage;
end;

function EFail.ToString : string;
begin
  Result := FMessage;
end;

{ -----------------------------------------------------------------------
  Pointer-array helpers
  The Items field is a raw block of pointer-sized slots (8 bytes on 64-bit).
  We never use 'array of' indexing on these raw blocks because SetLength
  is not a Blaise built-in.  Instead we manage the block via ReallocMem.
  ----------------------------------------------------------------------- }

const
  PtrSize = 8;  { bytes per pointer slot on 64-bit target }

type
  PPointer = ^Pointer;  { pointer to a pointer slot }

{ Read the I-th pointer slot from a raw block. }
function BlockGet(Block : Pointer; I : Int) : Pointer;
var
  Slot : PPointer;
begin
  Slot := PPointer(UInt(Block) + UInt(I) * PtrSize);
  Result := Slot^;
end;

{ Write a pointer into slot I of a raw block. }
procedure BlockSet(Block : Pointer; I : Int; Value : Pointer);
var
  Slot : PPointer;
begin
  Slot := PPointer(UInt(Block) + UInt(I) * PtrSize);
  Slot^ := Value;
end;

procedure CheckGrowSuiteList(AList : ^TSuiteList);
var
  NewCap : Int;
begin
  if AList^.Count < AList^.Capacity then
    Exit;
  if AList^.Capacity = 0 then
    NewCap := InitListLength
  else
    NewCap := AList^.Capacity * GrowFactor;
  AList^.Items := ReallocMem(AList^.Items, NewCap * PtrSize);
  AList^.Capacity := NewCap;
end;

procedure CheckGrowTestList(AList : ^TTestList);
var
  NewCap : Int;
begin
  if AList^.Count < AList^.Capacity then
    Exit;
  if AList^.Capacity = 0 then
    NewCap := InitListLength
  else
    NewCap := AList^.Capacity * GrowFactor;
  AList^.Items := ReallocMem(AList^.Items, NewCap * PtrSize);
  AList^.Capacity := NewCap;
end;

function SuiteListGet(AList : ^TSuiteList; I : Int) : ^TSuite;
begin
  Result := PSuite(BlockGet(AList^.Items, I));
end;

procedure SuiteListSet(AList : ^TSuiteList; I : Int; Value : ^TSuite);
begin
  BlockSet(AList^.Items, I, Value);
end;

function TestListGet(AList : ^TTestList; I : Int) : ^TTest;
begin
  Result := PTest(BlockGet(AList^.Items, I));
end;

procedure TestListSet(AList : ^TTestList; I : Int; Value : ^TTest);
begin
  BlockSet(AList^.Items, I, Value);
end;

{ -----------------------------------------------------------------------
  Hook accessors
  ----------------------------------------------------------------------- }

function SetSuiteStartHandler(AHandler : TSuiteStartHandler) : TSuiteStartHandler;
begin
  Result := GlobalSuiteStartHandler;
  GlobalSuiteStartHandler := AHandler;
end;

function SetTestStartHandler(AHandler : TTestStartHandler) : TTestStartHandler;
begin
  Result := GlobalTestStartHandler;
  GlobalTestStartHandler := AHandler;
end;

function SetTestCompleteHandler(AHandler : TTestCompleteHandler) : TTestCompleteHandler;
begin
  Result := GlobalTestCompleteHandler;
  GlobalTestCompleteHandler := AHandler;
end;

function SetSuiteCompleteHandler(AHandler : TSuiteCompleteHandler) : TSuiteCompleteHandler;
begin
  Result := GlobalSuiteCompleteHandler;
  GlobalSuiteCompleteHandler := AHandler;
end;

function SetRunCompleteHandler(AHandler : TRunCompleteHandler) : TRunCompleteHandler;
begin
  Result := GlobalRunCompleteHandler;
  GlobalRunCompleteHandler := AHandler;
end;

function SetRunStartHandler(AHandler : TRunStartHandler) : TRunStartHandler;
begin
  Result := GlobalRunStartHandler;
  GlobalRunStartHandler := AHandler;
end;

function SetSuiteSetupFailureHandler(AHandler : TSuiteSetupFailureHandler) : TSuiteSetupFailureHandler;
begin
  Result := GlobalSuiteSetupFailureHandler;
  GlobalSuiteSetupFailureHandler := AHandler;
end;

function SetSuiteTearDownFailureHandler(AHandler : TSuiteTearDownFailureHandler) : TSuiteTearDownFailureHandler;
begin
  Result := GlobalSuiteTearDownFailureHandler;
  GlobalSuiteTearDownFailureHandler := AHandler;
end;

function GetSuiteStartHandler : TSuiteStartHandler;
begin
  Result := GlobalSuiteStartHandler;
end;

function GetTestStartHandler : TTestStartHandler;
begin
  Result := GlobalTestStartHandler;
end;

function GetTestCompleteHandler : TTestCompleteHandler;
begin
  Result := GlobalTestCompleteHandler;
end;

function GetSuiteCompleteHandler : TSuiteCompleteHandler;
begin
  Result := GlobalSuiteCompleteHandler;
end;

function GetRunStartHandler : TRunStartHandler;
begin
  Result := GlobalRunStartHandler;
end;

function GetRunCompleteHandler : TRunCompleteHandler;
begin
  Result := GlobalRunCompleteHandler;
end;

function GetSuiteSetupFailureHandler : TSuiteSetupFailureHandler;
begin
  Result := GlobalSuiteSetupFailureHandler;
end;

function GetSuiteTearDownFailureHandler : TSuiteTearDownFailureHandler;
begin
  Result := GlobalSuiteTearDownFailureHandler;
end;

procedure ClearTestHooks;
begin
  SetSuiteStartHandler(nil);
  SetTestStartHandler(nil);
  SetTestCompleteHandler(nil);
  SetSuiteCompleteHandler(nil);
  SetRunStartHandler(nil);
  SetRunCompleteHandler(nil);
  SetSuiteSetupFailureHandler(nil);
  SetSuiteTearDownFailureHandler(nil);
end;

{ -----------------------------------------------------------------------
  Error management
  ----------------------------------------------------------------------- }

const
  SErrUnknown             = 'Unknown error';
  SErrOK                  = 'OK';
  SErrTestsRunning        = 'Tests already running';
  SErrRegistryEmpty       = 'Testregistry empty';
  SErrNoMemory            = 'No memory available';
  SErrNoSuite             = 'No suite available';
  SErrNoSuiteName         = 'No suite name specified';
  SErrSuiteSetupFailed    = 'Suite setup failed';
  SErrSuiteTeardownFailed = 'Suite teardown failed';
  SErrDuplicateSuite      = 'Duplicate suite name';
  SErrSuiteInactive       = 'Attempt to run inactive suite';
  SErrNoTest              = 'No test specified';
  SErrNoTestName          = 'No test name specified';
  SErrDuplicateTest       = 'Duplicate test name specified';
  SErrTestNotInSuite      = 'Test not member of suite';
  SErrTestInactive        = 'Attempt to run inactive test';

function GetTestError : TTestError;
begin
  Result := CurrentError;
end;

function GetTestErrorMessage : string;
begin
  case GetTestError() of
    teOK                  : Result := SErrOK;
    teTestsRunning        : Result := SErrTestsRunning;
    teRegistryEmpty       : Result := SErrRegistryEmpty;
    teNoMemory            : Result := SErrNoMemory;
    teNoSuite             : Result := SErrNoSuite;
    teNoSuiteName         : Result := SErrNoSuiteName;
    teSuiteSetupFailed    : Result := SErrSuiteSetupFailed;
    teSuiteTeardownFailed : Result := SErrSuiteTeardownFailed;
    teDuplicateSuite      : Result := SErrDuplicateSuite;
    teSuiteInactive       : Result := SErrSuiteInactive;
    teNoTest              : Result := SErrNoTest;
    teNoTestName          : Result := SErrNoTestName;
    teDuplicateTest       : Result := SErrDuplicateTest;
    teTestNotInSuite      : Result := SErrTestNotInSuite;
    teTestInactive        : Result := SErrTestInactive;
  else
    Result := SErrUnknown;
  end;
end;

function SetTestError(AError : TTestError) : TTestError;
begin
  if (AError = teOK) or (CurrentError = teOK) then
    CurrentError := AError;
  Result := CurrentError;
  if (AError <> teOK) and (CurrentErrorAction = eaAbort) then
    Halt(1);
end;

function CombineError(Original, Additional : TTestError) : TTestError;
begin
  if Original = teOK then
    Result := Additional
  else
    Result := Original;
end;

function GetErrorAction : TErrorAction;
begin
  Result := CurrentErrorAction;
end;

function SetErrorAction(AError : TErrorAction) : TErrorAction;
begin
  Result := CurrentErrorAction;
  CurrentErrorAction := AError;
end;

{ -----------------------------------------------------------------------
  Registry management
  ----------------------------------------------------------------------- }

function TestRegistryOK : Boolean;
begin
  Result := TestRegistry.Capacity > 0;
end;

procedure InitSuiteList(var Suites : TSuiteList);
begin
  Suites.Count := 0;
  Suites.Capacity := 0;
  Suites.Items := nil;
  CheckGrowSuiteList(@Suites);
end;

procedure DoSetupTestRegistry;
begin
  if TestRegistry.Count <> 0 then exit;
  InitSuiteList(TestRegistry);
end;

procedure FreeSuiteList(var Suites : TSuiteList); overload; forward;

procedure FreeSuite(ASuite : ^TSuite);
var
  I : Int;
begin
  FreeSuiteList(ASuite^.Suites);
  for I := 0 to ASuite^.Tests.Count - 1 do
    FreeMem(TestListGet(@ASuite^.Tests, I));
  if ASuite^.Tests.Items <> nil then
    FreeMem(ASuite^.Tests.Items);
  FreeMem(ASuite);
end;

procedure FreeSuiteList(var Suites : TSuiteList); overload;
var
  I : Int;
begin
  for I := 0 to Suites.Count - 1 do
    FreeSuite(SuiteListGet(@Suites, I));
  if Suites.Items <> nil then
    FreeMem(Suites.Items);
  Suites.Items := nil;
  Suites.Count := 0;
  Suites.Capacity := 0;
end;

function SetupTestRegistry : TTestError;
begin
  Result := SetTestError(teOK);
  Result := TearDownTestRegistry();
  if Result = teOK then
    DoSetupTestRegistry();
end;

function TearDownTestRegistry : TTestError;
begin
  SetTestError(teOK);
  FreeSuiteList(TestRegistry);
  Result := GetTestError();
end;

{ -----------------------------------------------------------------------
  Suite management
  ----------------------------------------------------------------------- }

function CheckInactive : Boolean;
begin
  Result := CurrentSuite = nil;
  if not Result then
    SetTestError(teTestsRunning);
end;

function AddSuite(const AName : string; AParent : ^TSuite) : ^TSuite; overload;
begin
  Result := AddSuite(AName, nil, nil, AParent, False);
end;

function GetSuiteCountInternal(AList : ^TSuiteList; Recurse : Boolean) : Int;
var
  I    : Int;
  Sub  : ^TSuite;
begin
  Result := AList^.Count;
  if Recurse then
    for I := 0 to AList^.Count - 1 do
      begin
      Sub := SuiteListGet(AList, I);
      Result := Result + GetSuiteCountInternal(@Sub^.Suites, True);
      end;
end;

function GetSuiteCount : Int; overload;
begin
  Result := GetSuiteCount(True);
end;

function GetSuiteCount(Recurse : Boolean) : Int; overload;
begin
  Result := GetSuiteCountInternal(@TestRegistry, Recurse);
end;

function GetSuiteCount(ASuite : ^TSuite) : Int; overload;
begin
  Result := GetSuiteCount(ASuite, True);
end;

function GetSuiteCount(ASuite : ^TSuite; Recurse : Boolean) : Int; overload;
begin
  if ASuite = nil then
    Result := 0
  else
    Result := GetSuiteCountInternal(@ASuite^.Suites, Recurse);
end;

function GetSuiteIndexInternal(AList : ^TSuiteList; const AName : string) : Int;
begin
  Result := -1;
  if AList = nil then
    begin
    SetTestError(teNoSuite);
    Exit;
    end;
  SetTestError(teOK);
  Result := AList^.Count - 1;
  while (Result >= 0) and (SuiteListGet(AList, Result)^.Name <> AName) do
    Dec(Result);
end;

function GetSuiteIndex(const AName : string) : Int; overload;
begin
  Result := GetSuiteIndexInternal(@TestRegistry, AName);
end;

function GetSuiteIndex(ASuite : ^TSuite; const AName : string) : Int; overload;
begin
  if ASuite = nil then
    Result := 0
  else
    Result := GetSuiteIndexInternal(@ASuite^.Suites, AName);
end;

function GetSuiteByName(AList : ^TSuiteList; const AName : string) : ^TSuite;
var
  I, P : Int;
  N : string;
  L : ^TSuiteList;
begin
  if AList = nil then
    begin
    Result := nil;
    Exit;
    end;
  N := AName;
  L := AList;
  P := 0;
  for I := 1 to Length(N) do
    if N[I] = '.' then
      P := I;
  if P > 0 then
    begin
    Result := GetSuiteByName(L, Copy(N, 1, P - 1));
    if Result <> nil then
      L := @Result^.Suites
    else
      L := nil;
    Delete(N, 1, P);
    end;
  I := GetSuiteIndexInternal(L, N);
  if I < 0 then
    Result := nil
  else
    Result := SuiteListGet(L, I);
end;

function GetSuite(const AIndex : Int) : ^TSuite; overload;
begin
  if (AIndex >= 0) and (AIndex < TestRegistry.Count) then
    Result := SuiteListGet(@TestRegistry, AIndex)
  else
    Result := nil;
end;

function GetSuite(const AName : string) : ^TSuite; overload;
begin
  Result := GetSuite(AName, nil);
end;

function GetSuite(const AName : string; AParent : ^TSuite) : ^TSuite; overload;
var
  L : ^TSuiteList;
begin
  Result := nil;
  if AParent <> nil then
    L := @AParent^.Suites
  else
    L := @TestRegistry;
  if L <> nil then
    Result := GetSuiteByName(L, AName);
end;

function AddSuite(const AName : string; ASetup : TTestSetup;
  ATearDown : TTestTearDown; AParent : ^TSuite;
  aPerTestSetupTearDown : Boolean) : ^TSuite; overload;
var
  S : ^TSuite;
  L : ^TSuiteList;
begin
  Result := nil;
  SetTestError(teOK);
  if not CheckInactive() then
    exit;
  DoSetupTestRegistry();
  if AName = '' then
    begin
    SetTestError(teNoSuiteName);
    Exit;
    end;
  S := GetSuite(AName, AParent);
  if S <> nil then
    begin
    SetTestError(teDuplicateSuite);
    Exit;
    end;
  if AParent <> nil then
    L := @AParent^.Suites
  else
    L := @TestRegistry;
  CheckGrowSuiteList(L);
  Result := PSuite(GetMem(SizeOf(TSuite)));
  if Result = nil then
    SetTestError(teNoMemory)
  else
    begin
    ZeroMem(Result, SizeOf(TSuite));
    Result^.Name := AName;
    Result^.Setup := ASetup;
    Result^.Teardown := ATearDown;
    Result^.Options := [];
    if aPerTestSetupTearDown then
      Include(Result^.Options, soSetupTearDownPerTest);
    Result^.ParentSuite := AParent;
    SuiteListSet(L, L^.Count, Result);
    Inc(L^.Count);
    end;
end;

{ -----------------------------------------------------------------------
  Test management
  ----------------------------------------------------------------------- }

function DoAddTest(const ATestName : string; const ASuite : ^TSuite) : ^TTest;
var
  I : Int;
begin
  Result := nil;
  SetTestError(teOK);
  if not CheckInactive() then
    Exit;
  if ASuite = nil then
    SetTestError(teNoSuite)
  else if ATestName = '' then
    SetTestError(teNoTestName)
  else
    begin
    I := GetTestIndex(ASuite, ATestName);
    if I <> -1 then
      SetTestError(teDuplicateTest)
    else
      begin
      CheckGrowTestList(@ASuite^.Tests);
      Result := PTest(GetMem(SizeOf(TTest)));
      if Result = nil then
        SetTestError(teNoMemory)
      else
        begin
        ZeroMem(Result, SizeOf(TTest));
        Result^.Name := ATestName;
        Result^.Options := [];
        TestListSet(@ASuite^.Tests, ASuite^.Tests.Count, Result);
        Inc(ASuite^.Tests.Count);
        end;
      end;
    end;
end;

function AddTest(const ATestName : string; ARun : TTestRun;
  const ASuite : ^TSuite) : ^TTest; overload;
begin
  Result := DoAddTest(ATestName, ASuite);
  if Assigned(Result) then
    Result^.Run := ARun;
end;

function AddTest(const ATestName : string; ARun : TTestRunProc;
  const ASuite : ^TSuite) : ^TTest; overload;
begin
  Result := DoAddTest(ATestName, ASuite);
  if Assigned(Result) then
    Result^.RunProc := ARun;
end;

function EnsureSuite(ASuiteName : string) : ^TSuite;
var
  SN : string;
begin
  SetTestError(teOK);
  SN := ASuiteName;
  if SN = '' then
    SN := DefaultSuiteName;
  Result := GetSuite(SN);
  if (Result = nil) and (ASuiteName <> '') then
    SetTestError(teNoSuite)
  else
    begin
    if Result = nil then
      Result := AddSuite(SN, nil, nil, nil, False);
    end;
end;

function AddTest(const ATestName : string; ARun : TTestRun;
  const ASuiteName : string) : ^TTest; overload;
var
  S : ^TSuite;
begin
  Result := nil;
  S := EnsureSuite(ASuiteName);
  if S <> nil then
    Result := AddTest(ATestName, ARun, S);
end;

function AddTest(const ATestName : string; ARun : TTestRunProc;
  const ASuiteName : string) : ^TTest; overload;
var
  S : ^TSuite;
begin
  Result := nil;
  S := EnsureSuite(ASuiteName);
  if S <> nil then
    Result := AddTest(ATestName, ARun, S);
end;

function GetTestIndex(const ASuiteName : string; const ATestName : string) : Int; overload;
begin
  Result := GetTestIndex(GetSuite(ASuiteName), ATestName);
end;

function GetTestIndex(const ASuite : ^TSuite; const ATestName : string) : Int; overload;
begin
  Result := -1;
  SetTestError(teOK);
  if ASuite = nil then
    SetTestError(teNoSuite)
  else
    begin
    Result := ASuite^.Tests.Count - 1;
    while (Result >= 0) and (TestListGet(@ASuite^.Tests, Result)^.Name <> ATestName) do
      Dec(Result);
    end;
end;

function GetTestIndex(const ASuite : ^TSuite; const ATest : ^TTest) : Int; overload;
begin
  SetTestError(teOK);
  Result := -1;
  if ASuite = nil then
    SetTestError(teNoSuite)
  else if ATest = nil then
    SetTestError(teNoTest)
  else
    begin
    Result := GetTestCount(ASuite) - 1;
    while (Result >= 0) and (ATest <> TestListGet(@ASuite^.Tests, Result)) do
      Dec(Result);
    end;
end;

function GetTestCount(const ASuiteName : string) : Int; overload;
begin
  Result := GetTestCount(GetSuite(ASuiteName));
end;

function GetTestCount(const ASuite : ^TSuite) : Int; overload;
begin
  SetTestError(teOK);
  Result := -1;
  if ASuite = nil then
    SetTestError(teNoSuite)
  else
    Result := ASuite^.Tests.Count;
end;

function GetTest(const ASuiteName : string; const ATestName : string) : PTest; overload;
begin
  Result := GetTest(GetSuite(ASuiteName), ATestName);
end;

function GetTest(const ASuite : ^TSuite; const ATestName : string) : ^TTest; overload;
var
  I, P : Int;
  N : string;
  S : ^TSuite;
begin
  Result := nil;
  N := ATestName;
  S := ASuite;
  P := 0;
  for I := 1 to Length(N) do
    if ATestName[I] = '.' then
      P := I;
  if P > 0 then
    begin
    S := GetSuite(Copy(N, 1, P - 1), S);
    Delete(N, 1, P);
    end;
  if S = nil then
    begin
    SetTestError(teNoSuite);
    Exit;
    end;
  I := GetTestIndex(S, N);
  if I = -1 then
    Result := nil
  else
    Result := TestListGet(@S^.Tests, I);
end;

function GetTest(const ASuite : ^TSuite; const ATestIndex : Int) : ^TTest; overload;
begin
  SetTestError(teOK);
  Result := nil;
  if ASuite = nil then
    SetTestError(teNoSuite)
  else if (ATestIndex >= 0) and (ATestIndex < GetTestCount(ASuite)) then
    Result := TestListGet(@ASuite^.Tests, ATestIndex);
end;

function TestIsInSuite(const ASuite : ^TSuite; const ATest : ^TTest) : Boolean;
begin
  Result := GetTestIndex(ASuite, ATest) <> -1;
end;

{ -----------------------------------------------------------------------
  Result record management
  ----------------------------------------------------------------------- }

procedure SetTestResultRec(var AResult : TResultRecord; AResultType : TTestResult;
  AMessage : string; Force : Boolean); overload;
var
  Prev : TTestResult;
begin
  if not ((AResult.TestResult = trEmpty) or Force) then
    Exit;
  Prev := AResult.TestResult;
  AResult.TestResult := AResultType;
  AResult.TestMessage := AMessage;
  if (Prev in [trEmpty, trOK]) and not (AResult.TestResult in [trEmpty, trOK])
      and (AResult.Test <> nil) then
    if AResult.TestResult = trTestIgnore then
      Inc(CurrentRun.TestsIgnored)
    else
      Inc(CurrentRun.TestsFailed);
end;

procedure SetTestResultRec(var AResult : TResultRecord; AResultType : TTestResult;
  AMessage : string); overload;
begin
  SetTestResultRec(AResult, AResultType, AMessage, False);
end;

procedure SetTestResult(AResultType : TTestResult; AMessage : string;
  Force : Boolean); overload;
begin
  if Assigned(CurrentResult) then
    SetTestResultRec(CurrentResult^, AResultType, AMessage, Force);
end;

procedure SetTestResult(AResultType : TTestResult; AMessage : string); overload;
begin
  SetTestResult(AResultType, AMessage, False);
end;

function DoAssert(AResult : Boolean; ACondition : string) : Boolean;
begin
  Inc(CurrentRun.AssertCount);
  Result := AResult;
  if (not Result) and Assigned(CurrentResult) then
    SetTestResultRec(CurrentResult^, trAssertFailed, ACondition);
end;

function CountResults(Results : ^TResultRecord) : Int;
begin
  Result := 0;
  while Results <> nil do
    begin
    Inc(Result);
    Results := Results^.NextResult;
    end;
end;

{ -----------------------------------------------------------------------
  Assertions
  ----------------------------------------------------------------------- }

function Ignore(const Msg : string) : Boolean;
begin
  SetTestResultRec(CurrentResult^, trTestIgnore, Msg);
  Result := False;
end;

function Fail(const Msg : string) : Boolean;
begin
  Result := DoAssert(False, Msg);
end;

function FailExit(const Msg : string) : Boolean;
begin
  Result := False;
  raise EFail.Create(Msg);
end;

function IgnoreExit(const Msg : string) : Boolean;
begin
  Result := False;
  raise EIgnore.Create(Msg);
end;

function AssertPassed : Boolean; overload;
begin
  Result := AssertPassed('');
end;

function AssertPassed(AMessage : string) : Boolean; overload;
begin
  Result := DoAssert(True, '');
  if Assigned(CurrentResult) then
    SetTestResultRec(CurrentResult^, trOK, AMessage);
end;

function AssertTrue(const AMessage : string; ACondition : Boolean) : Boolean;
begin
  DoAssert(ACondition, AMessage);
  Result := ACondition;
end;

function AssertFalse(const AMessage : string; ACondition : Boolean) : Boolean;
begin
  Result := AssertTrue(AMessage, not ACondition);
end;

function ExpectMessage(const AExpect, AActual : string;
  Quote : Boolean) : string; overload;
var
  E, A : string;
begin
  E := AExpect;
  A := AActual;
  if Quote then
    begin
    E := '"' + E + '"';
    A := '"' + A + '"';
    end;
  Result := 'Expected: ' + E + ' Actual: ' + A;
end;

function ExpectMessage(const AExpect, AActual : string) : string; overload;
begin
  Result := ExpectMessage(AExpect, AActual, False);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : string) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(AExpected, AActual, True),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Boolean) : Boolean; overload;
var
  SE, SA : string;
begin
  if AExpected then SE := 'True' else SE := 'False';
  if AActual   then SA := 'True' else SA := 'False';
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(SE, SA),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Byte) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(IntToStr(AExpected), IntToStr(AActual)),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Int32) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(IntToStr(AExpected), IntToStr(AActual)),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : UInt32) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(IntToStr(AExpected), IntToStr(AActual)),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Int64) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(Int64ToStr(AExpected), Int64ToStr(AActual)),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : UInt64) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(UInt64ToStr(AExpected), UInt64ToStr(AActual)),
    AExpected = AActual);
end;

function AssertEquals(AMessage : string; const AExpected, AActual, ADelta : Float64) : Boolean; overload;
var
  Effective : Float64;
begin
  Effective := ADelta;
  if Effective = 0 then
    Effective := DefaultDoubleDelta;
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(DoubleToStr(AExpected), DoubleToStr(AActual)),
    Abs(AExpected - AActual) < Effective);
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Float64) : Boolean; overload;
begin
  Result := AssertEquals(AMessage, AExpected, AActual, 0.0);
end;

function AssertNull(AMessage : string; const AValue : Pointer) : Boolean;
begin
  Result := AssertEquals(AMessage, Pointer(nil), AValue);
end;

function AssertNotNull(AMessage : string; const AValue : Pointer) : Boolean;
begin
  Result := AssertDiffers(AMessage, Pointer(nil), AValue);
end;

function PointerToHex(P : Pointer) : string;
const
  HexChars = '0123456789ABCDEF';
var
  V : UInt;
  S : string;
  I : Int;
begin
  if P = nil then
    begin
    Result := 'nil';
    Exit;
    end;
  V := UInt(P);
  S := '';
  for I := 1 to 16 do
    begin
    S := Copy(HexChars, V and $F, 1) + S;   { Blaise strings are 0-based }
    V := V shr 4;
    end;
  Result := '0x' + S;
end;

function AssertEquals(AMessage : string; const AExpected, AActual : Pointer) : Boolean; overload;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(PointerToHex(AExpected), PointerToHex(AActual)),
    AExpected = AActual);
end;

function AssertDiffers(AMessage : string; const AExpected, AActual : Pointer) : Boolean;
begin
  Result := AssertTrue(
    AMessage + '. ' + ExpectMessage(PointerToHex(AExpected), PointerToHex(AActual)),
    AExpected <> AActual);
end;

function AssertSame(AMessage : string; const AExpected, AActual : TObject) : Boolean;
begin
  Result := AssertEquals(AMessage, Pointer(AExpected), Pointer(AActual));
end;

function AssertNotSame(AMessage : string; const AExpected, AActual : TObject) : Boolean;
begin
  Result := AssertDiffers(AMessage, Pointer(AExpected), Pointer(AActual));
end;

function AssertInheritsFromClass(AMessage : string; const AChild, AParent : Pointer) : Boolean;
begin
  Result := AssertTrue(AMessage, AChild.InheritsFrom(AParent));
end;

function AssertInheritsFrom(AMessage : string; const AChild, AParent : TObject) : Boolean;
begin
  Result := AssertInheritsFromClass(AMessage, AChild.ClassType, AParent.ClassType);
end;

function AssertException(const AMessage : string; AExceptionClass : Pointer;
  ARun : TTestRun) : Boolean;
var
  Raised : Boolean;
  S : string;
begin
  Raised := False;
  S := '';
  try
    S := ARun();
  except
    on E : TObject do
      begin
      Raised := True;
      if (AExceptionClass <> nil) and
         not E.ClassType.InheritsFrom(AExceptionClass) then
        S := AMessage + ': unexpected exception class ' + E.ClassName;
      end;
  end;
  Result := AssertTrue(AMessage + ': expected exception was not raised', Raised)
    and AssertEquals(AMessage, '', S);
end;

function ExpectException(AMessage : string; AClass : Pointer) : Boolean;
begin
  Result := SetTestError(teOK) = teOK;
  Result := AssertTrue(AMessage, Result and Assigned(CurrentResult)
    and (CurrentResult^.TestResult in [trEmpty, trOK]));
  if Result then
    begin
    CurrentResult^.ExpectException := AClass;
    CurrentResult^.TestMessage := AMessage;
    end;
end;

{ -----------------------------------------------------------------------
  Result tree helpers
  ----------------------------------------------------------------------- }

procedure FreeResultRecord(P : ^TResultRecord; Recurse : Boolean);
var
  N : ^TResultRecord;
begin
  if not Assigned(P) then
    exit;
  repeat
    N := P^.NextResult;
    if Recurse then
      FreeResultRecord(P^.ChildResults, Recurse);
    FreeMem(P);
    P := N;
  until P = nil;
end;

procedure ZeroRunSummary(var ARun : TRunSummary);
begin
  ZeroMem(@ARun, SizeOf(TRunSummary));
end;

procedure ResetRun(var ARun : TRunSummary);
begin
  FreeResultRecord(ARun.Results.ChildResults, True);
  ZeroRunSummary(ARun);
  CurrentSuiteResult := @ARun.Results;
  CurrentResult := @ARun.Results;
end;

function ContinueTest(AResult : TTestError) : Boolean;
begin
  Result := (AResult = teOK) or (CurrentErrorAction = eaIgnore);
end;

function AllocateCurrentSuiteResult(ASuite : ^TSuite; IsChild : Boolean) : TTestError;
var
  P : ^TResultRecord;
begin
  Result := SetTestError(teOK);
  P := PResultRecord(GetMem(SizeOf(TResultRecord)));
  if P = nil then
    SetTestError(teNoMemory)
  else
    begin
    ZeroMem(P, SizeOf(TResultRecord));
    P^.Suite := ASuite;
    if IsChild then
      begin
      CurrentSuiteResult^.ChildResults := P;
      P^.ParentResult := CurrentSuiteResult;
      end
    else
      begin
      CurrentSuiteResult^.NextResult := P;
      P^.ParentResult := CurrentSuiteResult^.ParentResult;
      end;
    CurrentSuiteResult := P;
    CurrentResult := CurrentSuiteResult;
    end;
end;

function AllocateCurrentResult(ASuite : ^TSuite; ATest : ^TTest) : TTestError;
var
  N, P : ^TResultRecord;
begin
  Result := SetTestError(teOK);
  P := PResultRecord(GetMem(SizeOf(TResultRecord)));
  if P = nil then
    SetTestError(teNoMemory)
  else
    begin
    ZeroMem(P, SizeOf(TResultRecord));
    P^.TestResult := trEmpty;
    P^.Suite := ASuite;
    P^.Test := ATest;
    P^.ExpectException := nil;
    N := CurrentSuiteResult^.ChildResults;
    if N = nil then
      begin
      CurrentSuiteResult^.ChildResults := P;
      P^.ParentResult := CurrentSuiteResult;
      end
    else
      begin
      while N^.NextResult <> nil do
        N := N^.NextResult;
      N^.NextResult := P;
      P^.ParentResult := N^.ParentResult;
      end;
    CurrentResult := P;
    end;
end;

{ -----------------------------------------------------------------------
  Protected hook calls
  ----------------------------------------------------------------------- }

function RunGlobalRunStartHandler(Count : Int; Suites : PSuiteArray) : TTestError;
begin
  Result := SetTestError(teOK);
  try
    GlobalRunStartHandler(Count, Suites);
  except
    on E : TObject do
      begin
      CurrentResult := @CurrentRun.Results;
      SetTestResult(trHandlerError, E.ToString(), True);
      Result := SetTestError(teRunStartHandler);
      end;
  end;
end;

function RunGlobalRunCompleteHandler(Run : TRunSummary) : TTestError;
begin
  Result := SetTestError(teOK);
  if Assigned(GlobalRunCompleteHandler) then
    try
      GlobalRunCompleteHandler(Run);
    except
      on E : TObject do
        begin
        CurrentResult := @CurrentRun.Results;
        SetTestResult(trHandlerError, E.ToString(), False);
        Result := SetTestError(teRunCompleteHandler);
        end;
    end;
end;

function RunGlobalSuiteStartHandler(ASuite : ^TSuite) : TTestError;
begin
  Result := SetTestError(teOK);
  if Assigned(GlobalSuiteStartHandler) then
    try
      GlobalSuiteStartHandler(ASuite);
    except
      on E : EIgnore do
        SetTestResult(trTestIgnore, E.ToString());
      on E : EFail do
        SetTestResult(trAssertFailed, E.ToString());
      on E : TObject do
        SetTestResult(trHandlerError, E.ToString());
    end;
end;

function RunGlobalSuiteCompleteHandler(ASuite : ^TSuite;
  SuiteResult : ^TResultRecord) : TTestError;
var
  C : ^TResultRecord;
begin
  Result := SetTestError(teOK);
  if Assigned(GlobalSuiteCompleteHandler) then
    begin
    C := CurrentResult;
    CurrentResult := SuiteResult;
    try
      GlobalSuiteCompleteHandler(ASuite, SuiteResult);
    except
      on E : EIgnore do
        SetTestResult(trTestIgnore, E.ToString());
      on E : EFail do
        SetTestResultRec(SuiteResult^, trAssertFailed, E.ToString());
      on E : TObject do
        SetTestResultRec(SuiteResult^, trHandlerError, E.ToString());
    end;
    CurrentResult := C;
    end;
end;

function RunSuiteSetup(ASuite : ^TSuite; SuiteResult : ^TResultRecord) : TTestError;
var
  S       : string;
  SetupFn : TTestSetup;
begin
  Result := SetTestError(teOK);
  SetupFn := ASuite^.Setup;
  if not Assigned(SetupFn) then
    exit;
  S := '';
  try
    S := SetupFn();
  except
    on E : TObject do
      S := E.ToString();
  end;
  if S <> '' then
    begin
    SetTestResultRec(SuiteResult^, trSuiteSetupFailed, S, True);
    Result := SetTestError(teSuiteSetupFailed);
    Inc(CurrentRun.SuitesFailed);
    if Assigned(GlobalSuiteSetupFailureHandler) then
      GlobalSuiteSetupFailureHandler(ASuite, S);
    end;
end;

function RunSuiteTearDown(ASuite : ^TSuite; SuiteResult : ^TResultRecord) : TTestError;
var
  S          : string;
  C          : ^TResultRecord;
  TearDownFn : TTestTearDown;
begin
  Result := SetTestError(teOK);
  TearDownFn := ASuite^.Teardown;
  if not Assigned(TearDownFn) then
    exit;
  C := CurrentResult;
  CurrentResult := SuiteResult;
  S := '';
  try
    S := TearDownFn();
  except
    on E : TObject do
      S := E.ToString();
  end;
  if S <> '' then
    begin
    SetTestResultRec(SuiteResult^, trSuiteTearDownFailed, S, True);
    Result := SetTestError(teSuiteTeardownFailed);
    Inc(CurrentRun.SuitesFailed);
    if Assigned(GlobalSuiteTearDownFailureHandler) then
      GlobalSuiteTearDownFailureHandler(ASuite, S);
    end;
  CurrentResult := C;
end;

const
  SErrNoTestProcedure = 'No test procedure';

function RunTestHandler(aTest : ^TTest) : string;
var
  ExcRaised   : Boolean;
  ExcClass    : Pointer;
  ExcClassName : string;
  EM          : string;
  RunFn       : TTestRun;
  RunProcFn   : TTestRunProc;
begin
  Result := '';
  ExcRaised    := False;
  ExcClass     := nil;
  ExcClassName := '';
  EM := '';
  RunFn     := aTest^.Run;
  RunProcFn := aTest^.RunProc;
  try
    if Assigned(RunFn) then
      Result := RunFn()
    else if Assigned(RunProcFn) then
      begin
      Result := '';
      RunProcFn();
      end
    else
      Result := SErrNoTestProcedure;
  except
    on E : TObject do
      begin
      ExcRaised    := True;
      ExcClass     := E.ClassType;
      ExcClassName := E.ClassName;
      EM := E.ToString();
      end;
  end;
  if CurrentResult^.ExpectException <> nil then
    begin
    if not ExcRaised then
      Result := CurrentResult^.TestMessage + ' ' +
        ExpectMessage('<exception>', 'none raised')
    else if not ExcClass.InheritsFrom(CurrentResult^.ExpectException) then
      Result := CurrentResult^.TestMessage + ' ' +
        ExpectMessage('<expected class>', ExcClassName);
    end
  else
    begin
    { No exception expected — any exception is a failure. }
    if ExcRaised then
      Result := EM;
    end;
end;

{ -----------------------------------------------------------------------
  Suite stats
  ----------------------------------------------------------------------- }

procedure GetResultStats(AResults : ^TResultRecord; var Stats : TSuiteStats);
begin
  if AResults^.Test <> nil then
    begin
    Inc(Stats.TestsRun);
    case AResults^.TestResult of
      trEmpty        : Inc(Stats.TestsUnimplemented);
      trAssertFailed : Inc(Stats.TestsFailed);
      trTestInactive : Inc(Stats.TestsInactive);
      trTestIgnore   : Inc(Stats.TestsIgnored);
      trTestError    : Inc(Stats.TestsError);
    else
      { trOK and others: nothing to count }
    end;
    end;
end;

procedure DoGetSuiteStats(AResults : ^TResultRecord; var Stats : TSuiteStats);
var
  R : ^TResultRecord;
begin
  if AResults^.Test <> nil then
    Exit;
  Inc(Stats.Suites);
  R := AResults^.ChildResults;
  while R <> nil do
    begin
    if R^.Test = nil then
      DoGetSuiteStats(R, Stats)
    else
      GetResultStats(R, Stats);
    R := R^.NextResult;
    end;
end;

procedure GetSuiteStats(AResults : ^TResultRecord; out Stats : TSuiteStats);
begin
  ZeroMem(@Stats, SizeOf(TSuiteStats));
  DoGetSuiteStats(AResults, Stats);
end;

{ -----------------------------------------------------------------------
  Running a single test
  ----------------------------------------------------------------------- }

{ Stage constants for RunSingleTest: 0=StartHandler 1=Setup 2=Run 3=TearDown 4=CompleteHandler }
const
  stStartHandler   = 0;
  stSetup          = 1;
  stRun            = 2;
  stTearDown       = 3;
  stCompleteHandler = 4;

function TestStagePrefix(Stage : Int) : string;
begin
  case Stage of
    stStartHandler   : Result := 'Test start handler';
    stSetup          : Result := 'Test Setup';
    stTearDown       : Result := 'Test TearDown';
    stCompleteHandler : Result := 'Test complete handler';
  else Result := '';
  end;
end;

function TestStageError(Stage : Int) : TTestResult;
begin
  case Stage of
    stStartHandler   : Result := trHandlerError;
    stSetup          : Result := trSuiteSetupFailed;
    stTearDown       : Result := trSuiteTearDownFailed;
    stCompleteHandler : Result := trHandlerError;
  else Result := trTestError;
  end;
end;

function RunSingleTest(T : ^TTest) : TTestError;
var
  S             : string;
  Stage         : Int;
  CurrentAsserts : Int;
begin
  SetTestError(teOK);
  if CurrentSuite = nil then Halt(1);  { assertion: CurrentSuite must be set }
  CurrentTest := T;
  try
    CurrentAsserts := CurrentRun.AssertCount;
    Result := AllocateCurrentResult(CurrentSuite, T);
    if Result <> teOK then
      Exit;
    Stage := stStartHandler;
    if Assigned(GlobalTestStartHandler) then
      GlobalTestStartHandler(T, CurrentSuite);
    if soSetupTearDownPerTest in CurrentSuite^.Options then
      begin
      Stage := stSetup;
      Result := RunSuiteSetup(CurrentSuite, CurrentResult);
      end;
    if Result = teOK then
      if not (toInactive in T^.Options) then
        begin
        try
          Stage := stRun;
          S := RunTestHandler(T);
          if S <> '' then
            Fail(S)
          else if CurrentResult^.TestResult = trEmpty then
            if (CurrentAsserts = CurrentRun.AssertCount) and RequirePassed then
              Inc(CurrentRun.TestsUnimplemented)
            else
              SetTestResult(trOK, '');
        finally
          Inc(CurrentRun.TestsRun);
        end;
        if soSetupTearDownPerTest in CurrentSuite^.Options then
          begin
          Stage := stTearDown;
          Result := RunSuiteTearDown(CurrentSuite, CurrentResult);
          end;
        Stage := stCompleteHandler;
        end
      else
        begin
        Inc(CurrentRun.TestsInactive);
        SetTestResult(trTestInactive, '', True);
        Result := SetTestError(teTestInactive);
        end;
    if Assigned(GlobalTestCompleteHandler) then
      GlobalTestCompleteHandler(T, CurrentSuite, CurrentResult);
  except
    on E : TObject do
      begin
      S := TestStagePrefix(Stage);
      if S <> '' then S := '[' + S + '] ';
      S := S + E.ToString();
      SetTestResultRec(CurrentResult^, TestStageError(Stage), S, True);
      end;
  end;
  CurrentTest := nil;
end;

{ -----------------------------------------------------------------------
  Running a suite
  ----------------------------------------------------------------------- }

function SuiteStagePrefix(Stage : Int) : string;
begin
  case Stage of
    stStartHandler : Result := 'Start handler';
    stSetup        : Result := 'Setup';
    stTearDown     : Result := 'Teardown';
    stCompleteHandler : Result := 'End Handler';
  else Result := '';
  end;
end;

function SuiteStageError(Stage : Int) : TTestResult;
begin
  case Stage of
    stStartHandler    : Result := trHandlerError;
    stSetup           : Result := trSuiteSetupFailed;
    stTearDown        : Result := trSuiteTearDownFailed;
    stCompleteHandler : Result := trHandlerError;
  else Result := trTestError;
  end;
end;

function RunSingleSuite(ASuite : ^TSuite; IsChild : Boolean) : TTestError;
var
  S               : string;
  T               : ^TTest;
  Stage           : Int;
  I               : Int;
  R2              : TTestError;
  OldCurrentSuite : ^TSuite;
  SuiteResult     : ^TResultRecord;
begin
  if AllocateCurrentSuiteResult(ASuite, IsChild) <> teOK then
    exit;
  SetTestError(teOK);
  OldCurrentSuite := CurrentSuite;
  SuiteResult := CurrentSuiteResult;
  CurrentSuite := ASuite;
  try
    Result := teOK;
    Stage := stStartHandler;
    RunGlobalSuiteStartHandler(ASuite);
    if soInactive in ASuite^.Options then
      Inc(CurrentRun.SuitesInactive)
    else
      begin
      S := '';
      try
        if not (soSetupTearDownPerTest in ASuite^.Options) then
          begin
          Stage := stSetup;
          Result := RunSuiteSetup(ASuite, SuiteResult);
          end;
        Stage := stRun;
        for I := 0 to ASuite^.Suites.Count - 1 do
          if (Result = teOK) or (CurrentErrorAction = eaIgnore) then
            Result := RunSingleSuite(SuiteListGet(@ASuite^.Suites, I), I = 0);
        CurrentSuiteResult := SuiteResult;
        CurrentResult := SuiteResult;
        for I := 0 to ASuite^.Tests.Count - 1 do
          if (Result = teOK) or (CurrentErrorAction = eaIgnore) then
            begin
            T := TestListGet(@ASuite^.Tests, I);
            if not (toInactive in T^.Options) then
              Result := RunSingleTest(T)
            else
              Inc(CurrentRun.TestsInactive);
            end;
        Stage := stTearDown;
        Result := RunSuiteTearDown(ASuite, SuiteResult);
      finally
        Inc(CurrentRun.SuitesRun);
      end;
      Stage := stCompleteHandler;
      R2 := RunGlobalSuiteCompleteHandler(ASuite, SuiteResult);
      if (Result = teOK) and (R2 <> teOK) then
        Result := R2;
      SetTestResultRec(SuiteResult^, trOK, '', False);
      end;
  except
    on E : TObject do
      begin
      S := SuiteStagePrefix(Stage);
      if S <> '' then S := '[' + S + '] ';
      S := S + E.ToString();
      SetTestResultRec(SuiteResult^, SuiteStageError(Stage), S, True);
      end;
  end;
  CurrentSuite := OldCurrentSuite;
end;

function DoRunTest(ASuite : ^TSuite; ATest : ^TTest) : TTestError;
var
  A : PSuiteArray;
  SuiteResult : ^TResultRecord;
begin
  A := nil;
  ResetRun(CurrentRun);
  if AllocateCurrentSuiteResult(ASuite, True) <> teOK then
    exit;
  Result := SetTestError(teOK);
  SuiteResult := CurrentResult;
  if Assigned(GlobalRunStartHandler) then
    begin
    A := PSuiteArray(GetMem(PtrSize));
    BlockSet(A, 0, ASuite);
    Result := RunGlobalRunStartHandler(1, A);
    FreeMem(A);
    A := nil;
    if not ContinueTest(Result) then
      exit;
    end;
  if soInactive in ASuite^.Options then
    begin
    SetTestResult(trSuiteInactive, '', True);
    Inc(CurrentRun.SuitesInactive);
    Inc(CurrentRun.SuitesFailed);
    RunGlobalRunCompleteHandler(CurrentRun);
    Result := SetTestError(teSuiteInactive);
    Exit;
    end;
  if not ContinueTest(Result) then
    begin
    Result := CombineError(Result, RunGlobalRunCompleteHandler(CurrentRun));
    exit;
    end;
  CurrentSuite := ASuite;
  try
    Result := RunGlobalSuiteStartHandler(ASuite);
    if ContinueTest(Result) then
      begin
      Result := RunSuiteSetup(ASuite, SuiteResult);
      if ContinueTest(Result) then
        begin
        Result := CombineError(Result, RunSingleTest(ATest));
        Result := CombineError(Result, RunSuiteTearDown(ASuite, SuiteResult));
        end;
      end;
  finally
    SetTestResultRec(SuiteResult^, trOK, '');
    Inc(CurrentRun.SuitesRun);
    CurrentSuite := nil;
  end;
  Result := CombineError(Result, RunGlobalSuiteCompleteHandler(ASuite, SuiteResult));
  Result := CombineError(Result, RunGlobalRunCompleteHandler(CurrentRun));
end;

function DoRunSuite(ASuite : ^TSuite) : TTestError;
var
  A : PSuiteArray;
begin
  A := nil;
  SetTestError(teOK);
  ResetRun(CurrentRun);
  if Assigned(GlobalRunStartHandler) then
    begin
    A := PSuiteArray(GetMem(PtrSize));
    BlockSet(A, 0, ASuite);
    Result := RunGlobalRunStartHandler(1, A);
    FreeMem(A);
    A := nil;
    if not ContinueTest(Result) then
      Exit;
    end;
  SetTestError(teOK);
  Result := teOK;
  Result := RunSingleSuite(ASuite, True);
  Result := CombineError(Result, RunGlobalRunCompleteHandler(CurrentRun));
end;

function RunSuite(ASuite : ^TSuite) : TTestError; overload;
begin
  SetTestError(teOK);
  if ASuite = nil then
    Result := SetTestError(teNoSuite)
  else
    Result := DoRunSuite(ASuite);
end;

function RunSuite(const ASuiteName : string) : TTestError; overload;
begin
  Result := RunSuite(GetSuite(ASuiteName));
end;

function RunSuite(ASuiteIndex : Int) : TTestError; overload;
begin
  Result := RunSuite(GetSuite(ASuiteIndex));
end;

function RunTest(ASuite : ^TSuite; const ATestName : string) : TTestError; overload;
begin
  Result := RunTest(ASuite, GetTest(ASuite, ATestName));
end;

function RunTest(const ASuiteName : string; const ATestName : string) : TTestError; overload;
var
  S : ^TSuite;
begin
  S := GetSuite(ASuiteName);
  Result := RunTest(S, GetTest(S, ATestName));
end;

function RunTest(ASuite : ^TSuite; ATest : ^TTest) : TTestError; overload;
begin
  Result := SetTestError(teOK);
  ProcessSysCommandline();
  if ASuite = nil then
    Result := SetTestError(teNoSuite)
  else if ATest = nil then
    Result := SetTestError(teNoTest)
  else if not TestIsInSuite(ASuite, ATest) then
    Result := SetTestError(teTestNotInSuite)
  else
    Result := DoRunTest(ASuite, ATest);
end;

function GetCurrentRun : TRunSummary;
begin
  Result := CurrentRun;
end;

function GetCurrentSuite : ^TSuite;
begin
  Result := CurrentSuite;
end;

function GetCurrentTest : PTest;
begin
  Result := CurrentTest;
end;

function GetCurrentResult : PResultRecord;
begin
  Result := CurrentResult;
end;

function RunAllTests : TTestError;
var
  I : Int;
  A : PSuiteArray;
begin
  A := nil;
  Result := SetTestError(teOK);
  ResetRun(CurrentRun);
  if Assigned(GlobalRunStartHandler) then
    begin
    A := PSuiteArray(GetMem(TestRegistry.Count * PtrSize));
    for I := 0 to TestRegistry.Count - 1 do
      BlockSet(A, I, SuiteListGet(@TestRegistry, I));
    GlobalRunStartHandler(TestRegistry.Count, A);
    FreeMem(A);
    A := nil;
    end;
  if TestRegistry.Count = 0 then
    Result := SetTestError(teRegistryEmpty)
  else
    begin
    I := 0;
    while (I < TestRegistry.Count) and ContinueTest(Result) do
      begin
      Result := CombineError(Result,
        RunSingleSuite(SuiteListGet(@TestRegistry, I), I = 0));
      Inc(I);
      end;
    end;
  Result := CombineError(Result, RunGlobalRunCompleteHandler(CurrentRun));
end;

procedure SysHalt;
begin
  if CurrentRun.TestsFailed <> 0 then
    Halt(1)
  else
    Halt(0);
end;

procedure DoRunSysTests(S : PSuite; T : PTest); overload; forward;

procedure RunTest(ARun : TTestRun); overload;
begin
  ProcessSysCommandLine();
  if ARun = nil then
    Halt(2);
  if AddTest('Global', ARun, '') = nil then
    Halt(3);
  DoRunSysTests(nil, nil);
end;

{ -----------------------------------------------------------------------
  System hooks — text output runner
  ----------------------------------------------------------------------- }

const
  STestRun             = 'Test run';
  SRunSummary          = 'Run summary';
  SSuites              = 'Suites';
  SSuite               = 'Suite';
  SSummary             = 'summary';
  SSuitesSummary       = 'Suites summary';
  STests               = 'Tests';
  STest                = 'Test';
  STestsSummary        = 'Tests summary';
  SInactiveCount       = 'Inactive';
  SIgnoredCount        = 'Ignored';
  SRunCount            = 'Run';
  SFailedCount         = 'Failed';
  SUnimplementedCount  = 'Unimplemented';
  SPassed              = 'Passed';
  SIgnored             = 'Ignored';
  SFailed              = 'Failed';
  SError               = 'Error';
  SInactive            = 'Inactive';
  SNotImplemented      = 'Not implemented';
  SUnknown             = 'Unknown';
  SErrorMessage        = 'Error message';
  SSuiteSetupFailed    = 'Suite setup failed';
  SSuiteTearDownFailed = 'Suite teardown failed';
  SUsage               = 'Usage:';
  SHelpL               = '-l --list         list all tests (observes -s)';
  SHelpF               = '-f --failures     only show names and errors of failed tests';
  SHelpH               = '-h --help         this help message';
  SHelpN               = '-n --normal       normal log level';
  SHelpO               = '-o --output=file  log output file name (default is standard output)';
  SHelpQ               = '-q --quiet        Do not display messages';
  SHelpS               = '-s --suite=name   Only run/list tests in given suite';
  SHelpT               = '-t --test=name    Only run/list tests matching given test (requires -s)';
  SHelpV               = '-v --verbose      Verbose output logging';
  SHelpExitCodes       = 'Possible exit codes:';
  SHelpExit0           = '0 - All actions (tests) completed successfully';
  SHelpExit1           = '1 - All tests were run, but some tests failed.';
  SHelpExit2           = '2 - An empty test function was given to RunTest';
  SHelpExit3           = '3 - The requested suite was not found';
  SHelpExit4           = '4 - The requested test was not found';
  SHelpExit5           = '5 - An unexpected error occurred in the test suite';

type
  TRunMode = (rmHelp, rmList, rmTest);

var
  CurrentRunMode    : TSysRunVerbosity;
  SysSuite          : PSuite;
  SysOutputFileName : string;
  SysTestName       : string;
  SysSuiteName      : string;
  SysRunMode        : TRunMode;
  SysSuiteIndent    : string;

procedure SysSuiteStartHandler(ASuite : PSuite);
begin
  if ASuite <> SysSuite then
    begin
    SysSuiteIndent := SysSuiteIndent + '  ';
    Write(SysSuiteIndent + SSuite + ' ' + ASuite^.Name + ':');
    if CurrentRunMode = rvVerbose then
      WriteLn(' (' + IntToStr(ASuite^.Tests.Count) + ' ' + STests + ')')
    else
      WriteLn();
    SysSuite := ASuite;
    end;
end;

procedure SysTestStartHandler(ATest : PTest; ASuite : PSuite);
begin
  if CurrentRunMode in [rvQuiet, rvFailures] then
    Exit;
  Write(SysSuiteIndent + '  ' + STest + ' ' + ATest^.Name + ': ');
end;

procedure SysTestCompleteHandler(ATest : PTest; ASuite : PSuite;
  const AResultRecord : PResultRecord);
var
  S : string;
  F, O : Boolean;
  TR : TTestResult;
begin
  if CurrentRunMode = rvQuiet then exit;
  F := CurrentRunMode = rvFailures;
  O := False;
  S := AResultRecord^.TestMessage;
  TR := AResultRecord^.TestResult;
  case TR of
    trEmpty :
      if not F then
        Write(SNotImplemented);
    trOK :
      if not F then
        Write(SPassed);
    trTestIgnore :
      if not F then
        Write(SIgnored + ' (' + S + ')');
    trSuiteSetupFailed,
    trSuiteTearDownFailed,
    trAssertFailed,
    trTestError,
    trHandlerError :
      begin
      if F then
        Write(STest + ' ' + ASuite^.Name + '.' + ATest^.Name + ': ');
      if TR in [trTestError, trHandlerError] then
        Write(SError)
      else
        Write(SFailed);
      Write(' (' + SErrorMessage + ': ' + S + ')');
      O := True;
      end;
    trTestInactive :
      if not F then
        Write(SInactive);
  else
    if not F then
      Write(SUnknown + ' : ' + AResultRecord^.TestMessage);
  end;
  if O or (not F) then
    WriteLn();
end;

procedure SysSuiteCompleteHandler(ASuite : PSuite;
  const AResults : PResultRecord);
var
  Stats : TSuiteStats;
begin
  if CurrentRunMode = rvFailures then
    Delete(SysSuiteIndent, 1, 2);
  if CurrentRunMode in [rvQuiet, rvFailures] then
    exit;
  Write(SysSuiteIndent + SSuite + ' ' + ASuite^.Name + ' ' + SSummary + ': ');
  GetSuiteStats(AResults, Stats);
  Write(SRunCount + ': ' + IntToStr(Stats.TestsRun) +
    ' ' + SFailedCount + ': ' + IntToStr(Stats.TestsFailed) +
    ' ' + SInactiveCount + ': ' + IntToStr(Stats.TestsInactive) +
    ' ' + SIgnoredCount + ': ' + IntToStr(Stats.TestsIgnored));
  if RequirePassed then
    Write(' ' + SUnimplementedCount + ': ' + IntToStr(Stats.TestsUnimplemented));
  WriteLn();
  Delete(SysSuiteIndent, 1, 2);
end;

procedure SysRunStartHandler(Count : Int; Suites : PSuiteArray);
var
  I, TC : Int;
begin
  if CurrentRunMode in [rvQuiet, rvFailures] then
    exit;
  TC := 0;
  for I := 0 to Count - 1 do
    Inc(TC, PSuite(BlockGet(Suites, I))^.Tests.Count);
  Write(STestRun + ':');
  if CurrentRunMode <> rvVerbose then
    WriteLn()
  else
    WriteLn(' ' + IntToStr(Count) + ' ' + SSuites +
      ', ' + IntToStr(TC) + ' ' + STests);
end;

procedure SysRunCompleteHandler(const AResult : TRunSummary);
begin
  if CurrentRunMode = rvQuiet then exit;
  if CurrentRunMode = rvFailures then
    begin
    WriteLn(SFailedCount + ': ' + IntToStr(AResult.TestsFailed));
    exit;
    end;
  WriteLn();
  WriteLn(SRunSummary + ':');
  if CurrentRunMode = rvVerbose then
    begin
    WriteLn('  ' + SSuitesSummary + ':');
    WriteLn('    ' + SRunCount + ': ' + IntToStr(AResult.SuitesRun));
    WriteLn('    ' + SFailedCount + ': ' + IntToStr(AResult.SuitesFailed));
    WriteLn('    ' + SInactiveCount + ': ' + IntToStr(AResult.SuitesInactive));
    WriteLn('  ' + STestsSummary + ':');
    WriteLn('    ' + SRunCount + ': ' + IntToStr(AResult.TestsRun));
    WriteLn('    ' + SInactiveCount + ': ' + IntToStr(AResult.TestsInactive));
    WriteLn('    ' + SFailedCount + ': ' + IntToStr(AResult.TestsFailed));
    WriteLn('    ' + SIgnoredCount + ': ' + IntToStr(AResult.TestsIgnored));
    if RequirePassed then
      WriteLn('    ' + SUnimplementedCount + ': ' +
        IntToStr(AResult.TestsUnimplemented));
    end
  else
    begin
    WriteLn('  ' + SSuitesSummary + ': ' +
      SRunCount + ': ' + IntToStr(AResult.SuitesRun) +
      ' ' + SFailedCount + ': ' + IntToStr(AResult.SuitesFailed) +
      ' ' + SInactiveCount + ': ' + IntToStr(AResult.SuitesInactive));
    Write('  ' + STestsSummary + ': ' +
      SRunCount + ': ' + IntToStr(AResult.TestsRun) +
      ' ' + SFailedCount + ': ' + IntToStr(AResult.TestsFailed) +
      ' ' + SInactiveCount + ': ' + IntToStr(AResult.TestsInactive) +
      ' ' + SIgnoredCount + ': ' + IntToStr(AResult.TestsIgnored));
    if RequirePassed then
      WriteLn(' ' + SUnimplementedCount + ': ' +
        IntToStr(AResult.TestsUnimplemented))
    else
      WriteLn();
    end;
end;

procedure SysSuiteSetupFailedHandler(ASuite : PSuite; const AError : string);
begin
  if CurrentRunMode = rvVerbose then
    WriteLn(SSuiteSetupFailed + ' : ' + ASuite^.Name + ' : ' + AError);
end;

procedure SysSuiteTearDownFailedHandler(ASuite : PSuite; const AError : string);
begin
  if CurrentRunMode = rvVerbose then
    WriteLn(SSuiteTearDownFailed + ' : ' + ASuite^.Name + ' : ' + AError);
end;

procedure SetupSysHandlers;
begin
  SetRunStartHandler(@SysRunStartHandler);
  SetRunCompleteHandler(@SysRunCompleteHandler);
  SetSuiteCompleteHandler(@SysSuiteCompleteHandler);
  SetSuiteStartHandler(@SysSuiteStartHandler);
  SetSuiteSetupFailureHandler(@SysSuiteSetupFailedHandler);
  SetSuiteTearDownFailureHandler(@SysSuiteTearDownFailedHandler);
  SetTestStartHandler(@SysTestStartHandler);
  SetTestCompleteHandler(@SysTestCompleteHandler);
end;

procedure TearDownSysHandlers;
begin
  ClearTestHooks();
end;

function GetSysRunVerbosity : TSysRunVerbosity;
begin
  Result := CurrentRunMode;
end;

function SetSysRunVerbosity(AMode : TSysRunVerbosity) : TSysRunVerbosity;
begin
  Result := CurrentRunMode;
  CurrentRunMode := AMode;
end;

function FullSuiteName(ASuite : PSuite) : string;
begin
  Result := '';
  while ASuite <> nil do
    begin
    if Result <> '' then
      Result := '.' + Result;
    Result := ASuite^.Name + Result;
    ASuite := ASuite^.ParentSuite;
    end;
end;

procedure SysListTests(ASuiteList : PSuiteList; ASuite : PSuite; ATest : PTest);
var
  I, J : Int;
  S : PSuite;
  T : PTest;
begin
  if ASuiteList = nil then
    exit;
  for I := 0 to ASuiteList^.Count - 1 do
    begin
    S := SuiteListGet(ASuiteList, I);
    if (ASuite = nil) or (ASuite = S) then
      begin
      if CurrentRunMode = rvVerbose then
        WriteLn(SSuite + ': ' + FullSuiteName(S));
      SysListTests(@S^.Suites, ASuite, ATest);
      for J := 0 to S^.Tests.Count - 1 do
        begin
        T := TestListGet(@S^.Tests, J);
        if (ATest = nil) or (ATest = T) then
          begin
          if CurrentRunMode = rvVerbose then
            Write('  ' + STest + ': ');
          WriteLn(FullSuiteName(S) + '.' + T^.Name);
          end;
        end;
      end;
    end;
end;

function TestO(const Short, Long : string; var AIdx : Int; var AStr : string) : Boolean;
var
  L : Int;
  LO : string;
begin
  Result := AStr = '-' + Short;
  if Result then
    begin
    Inc(AIdx);
    AStr := ParamStr(AIdx);
    end
  else
    begin
    LO := '--' + Long + '=';
    L := Length(LO);
    Result := Copy(AStr, 1, L) = LO;
    if Result then
      Delete(AStr, 1, L);
    end;
end;

procedure ProcessSysCommandline;
var
  I : Int;
  S : string;
begin
  SysRunMode := rmTest;
  I := 1;
  while I <= ParamCount() do
    begin
    S := ParamStr(I);
    if (S = '-v') or (S = '--verbose') then
      SetSysRunVerbosity(rvVerbose)
    else if (S = '-q') or (S = '--quiet') then
      SetSysRunVerbosity(rvQuiet)
    else if (S = '-n') or (S = '--normal') then
      SetSysRunVerbosity(rvNormal)
    else if (S = '-f') or (S = '--failures') then
      SetSysRunVerbosity(rvFailures)
    else if (S = '-l') or (S = '--list') then
      SysRunMode := rmList
    else if (S = '-h') or (S = '--help') then
      SysRunMode := rmHelp
    else if TestO('o', 'output', I, S) then
      SysOutputFileName := S
    else if TestO('s', 'suite', I, S) then
      SysSuiteName := S
    else if TestO('t', 'test', I, S) then
      SysTestName := S;
    Inc(I);
    end;
end;

procedure SysShowHelp;
begin
  WriteLn(SUsage);
  WriteLn(SHelpF);
  WriteLn(SHelpH);
  WriteLn(SHelpL);
  WriteLn(SHelpN);
  WriteLn(SHelpO);
  WriteLn(SHelpQ);
  WriteLn(SHelpS);
  WriteLn(SHelpT);
  WriteLn(SHelpV);
  WriteLn(SHelpExitCodes);
  WriteLn(SHelpExit0);
  WriteLn(SHelpExit1);
  WriteLn(SHelpExit2);
  WriteLn(SHelpExit3);
  WriteLn(SHelpExit4);
  WriteLn(SHelpExit5);
end;

procedure DoRunSysTests(S : PSuite; T : PTest); overload;
var
  R : TTestError;
begin
  case SysRunMode of
    rmHelp :
      begin
      SysShowHelp();
      Halt(0);
      end;
    rmList :
      begin
      SysListTests(@TestRegistry, S, T);
      Halt(0);
      end;
    rmTest :
      begin
      if Assigned(T) then
        R := RunTest(S, T)
      else if Assigned(S) then
        R := RunSuite(S)
      else
        R := RunAllTests();
      if R <> teOK then
        Halt(5)
      else
        SysHalt();
      end;
  end;
end;

procedure RunAllSysTests;
var
  S : PSuite;
  T : PTest;
  P : Int;
begin
  S := nil;
  T := nil;
  ProcessSysCommandline();
  P := Pos('.', SysTestName);
  if P > 0 then
    begin
    SysSuiteName := Copy(SysTestName, 1, P - 1);
    Delete(SysTestName, 1, P);
    P := Pos('.', SysTestName);
    while P <> 0 do
      begin
      SysSuiteName := SysSuiteName + '.' + Copy(SysTestName, 1, P - 1);
      Delete(SysTestName, 1, P);
      P := Pos('.', SysTestName);
      end;
    end;
  if SysSuiteName <> '' then
    begin
    S := GetSuite(SysSuiteName);
    if S = nil then
      Halt(3);
    end;
  if SysTestName <> '' then
    begin
    if S = nil then
      begin
      S := GetSuite(DefaultSuiteName);
      if S = nil then
        Halt(3);
      end;
    T := GetTest(S, SysTestName);
    if T = nil then
      Halt(4);
    end;
  DoRunSysTests(S, T);
end;

function GetSysTestOS : string;
begin
  Result := 'linux';
end;

{ -----------------------------------------------------------------------
  Initialisation
  ----------------------------------------------------------------------- }

initialization
  InitListLength   := 10;
  GrowFactor       := 2;
  DefaultSuiteName := 'Globals';
  RequirePassed    := False;
  DefaultDoubleDelta := 1E-14;
  CurrentRunMode   := rvNormal;
  SetupTestRegistry();
  SetupSysHandlers();

finalization
  TearDownSysHandlers();
  TearDownTestRegistry();
  ResetRun(CurrentRun);

end.
