{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  blaise.testing.runner.text — plain-text test runner for blaise.testing.

  Step 11e.  Walks the blaise.testing global registry, instantiates one
  TTestCase per published method per registered class, runs each
  against a single TTestResult, and prints PASS / FAIL output plus a
  summary line.

  CLI filtering (Step 15):
    --suite ClassName              run all tests in ClassName
    --suite ClassName.MethodName   run one specific test method
    --exclude-category Name        skip suites/methods marked [Category('Name')]

  --suite may be passed multiple times, and each value may be a
  comma-delimited list.  These three invocations are equivalent:
    ./TestRunner --suite TA --suite TB.m
    ./TestRunner --suite TA,TB.m
    ./TestRunner --suite TA --suite TB,TB.m

  When invoked by 'pasbuild test' no arguments are passed, so all
  registered tests run.

  ARC: TTestCase instances created via Cls.Create are released at
  loop-iteration end via the standard scope-based _ClassRelease the
  codegen emits for class-typed locals.  No explicit Free calls.
}

unit blaise.testing.runner.text;

interface

uses
  blaise.testing, Classes, Generics.Collections, SysUtils, Process;

{ Run every test method of every TTestCase class registered via
  RegisterTest.  Returns the result so the caller can compute an
  exit code or feed it to subsequent reporters. }
function RunRegisteredTests: TTestResult;

{ Print a one-line summary plus per-failure detail to standard output.
  Suitable for direct call after RunRegisteredTests. }
procedure PrintSummary(AResult: TTestResult);

{ Convenience: run, print, return 0 on all-green and 1 otherwise.
  Respects --suite / --suite Class.Method command-line filtering.
  Programs can do 'Halt(RunAll)' as the last statement. }
function RunAll: Integer;

{ Filter helpers — exposed for unit testing.  A filter list is a
  TList<String> where every entry is either a class-only filter ("TFooTests")
  or a class.method filter ("TFooTests.TestBar"). }

{ Split a single user-supplied filter spec into class and method parts.
  Comma is not handled here (callers split first). }
procedure SplitSuiteSpec(const ASpec: string;
  out ASuite: string; out AMethod: string);

{ Append ASpec to AFilters.  If ASpec contains commas, each
  comma-delimited entry is appended individually after trimming. }
procedure AppendSuiteFilter(AFilters: TList<String>; const ASpec: string);

{ True if the (ASuite, AMethod) pair matches at least one filter in
  AFilters.  An empty filter list always matches. }
function MatchesFilters(AFilters: TList<String>;
  const ASuite, AMethod: string): Boolean;

{ Parse a [Threaded] suite subprocess's --verbose output into AResult.
  Exposed for unit testing. }
procedure ParseSubprocessOutput(const AOutput: string; AResult: TTestResult);


implementation

{ -----------------------------------------------------------------------
  Published-method table walk

  Reads the typeinfo's slot 3 (methods table) for the given class
  metaclass value and climbs the parent chain so inherited published
  methods are visible.  Returns the count and i'th name through
  per-class out-helpers.

  Typeinfo and methods-table layout are documented in
  blaise.codegen.qbe.pas:EmitTypeInfoDefs.
  ----------------------------------------------------------------------- }

function PublishedMethodCount(ATestClass: TTestCaseClass): Integer;
var
  TInfo:   Pointer;
  Slot:    ^Pointer;
  Methods: Pointer;
  Count:   ^Int64;
begin
  Result := 0;
  TInfo  := Pointer(ATestClass);
  while TInfo <> nil do
  begin
    Slot    := TInfo + 24;       { typeinfo[3] = methods table ptr }
    Methods := Slot^;
    if Methods <> nil then
    begin
      Count  := Methods;
      Result := Result + Integer(Count^);
    end;
    Slot  := TInfo;              { typeinfo[0] = parent }
    TInfo := Slot^;
  end;
end;

{ Return the i'th published method name across the full parent chain.
  Methods declared in the class itself come first; parent methods
  follow.  Returns '' if AIndex is out of range. }
function PublishedMethodName(ATestClass: TTestCaseClass;
  AIndex: Integer): string;
var
  TInfo:   Pointer;
  Slot:    ^Pointer;
  Methods: Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  EntName: Pointer;
  Local:   Integer;
  Seen:    Integer;
  I:       Integer;
begin
  Result := '';
  Seen   := 0;
  TInfo  := Pointer(ATestClass);
  while TInfo <> nil do
  begin
    Slot    := TInfo + 24;
    Methods := Slot^;
    if Methods <> nil then
    begin
      Count := Methods;
      Local := Integer(Count^);
      if AIndex < Seen + Local then
      begin
        { The wanted entry lives in this class's own table. }
        Entry := Methods + 8;
        for I := 0 to (AIndex - Seen) - 1 do
          Entry := Pointer(Entry) + 24;     { skip (name, addr, sig) triple }
        EntName := Entry^;
        Exit(string(PChar(EntName)));
      end;
      Seen := Seen + Local;
    end;
    Slot  := TInfo;
    TInfo := Slot^;
  end;
end;

{ Return the i'th published method's parameter-kind signature — the third
  field of its methods-table triple (see MethodParamSig in the codegen:
  'i'/'I'/'b'/'s'/'d'/'x' per param, '' = parameterless).  Drives the
  [TestCase] typed dispatch in TTestCase.RunTest. }
function PublishedMethodSig(ATestClass: TTestCaseClass;
  AIndex: Integer): string;
var
  TInfo:   Pointer;
  Slot:    ^Pointer;
  Methods: Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  EntSig:  Pointer;
  Local:   Integer;
  Seen:    Integer;
  I:       Integer;
begin
  Result := '';
  Seen   := 0;
  TInfo  := Pointer(ATestClass);
  while TInfo <> nil do
  begin
    Slot    := TInfo + 24;
    Methods := Slot^;
    if Methods <> nil then
    begin
      Count := Methods;
      Local := Integer(Count^);
      if AIndex < Seen + Local then
      begin
        Entry := Methods + 8;
        for I := 0 to (AIndex - Seen) - 1 do
          Entry := Pointer(Entry) + 24;
        Entry  := Pointer(Entry) + 16;      { third field of the triple }
        EntSig := Entry^;
        if EntSig = nil then Exit('');
        Exit(string(PChar(EntSig)));
      end;
      Seen := Seen + Local;
    end;
    Slot  := TInfo;
    TInfo := Slot^;
  end;
end;

{ True when the method (or its class) carries [Category(ACat)].  Both the
  method-level attributes and a class-level category are consulted. }
function MethodInCategory(ATestClass: TTestCaseClass;
  const AMethName, ACat: string): Boolean;
var
  I, N: Integer;
  A:    TObject;
begin
  Result := False;
  N := MethodAttributeCount(ATestClass, AMethName);
  for I := 0 to N - 1 do
  begin
    A := GetMethodAttributeAt(ATestClass, AMethName, I);
    if (A is CategoryAttribute) and
       SameText(CategoryAttribute(A).Name, ACat) then
      Exit(True);
  end;
  A := GetClassAttribute(ATestClass, CategoryAttribute);
  if (A <> nil) and SameText(CategoryAttribute(A).Name, ACat) then
    Result := True;
end;

{ Return the class name of a TTestCaseClass by reading typeinfo[2]
  (offset 16) — the immortal Blaise string emitted by EmitClassNameRef.
  Same read pattern as PublishedMethodName uses for method name entries. }
function TestClassName(ATestClass: TTestCaseClass): string;
var
  TInfo:    Pointer;
  NameSlot: ^Pointer;
begin
  TInfo    := Pointer(ATestClass);
  NameSlot := TInfo + 16;           { typeinfo[2] = class name string ptr }
  Result   := string(PChar(NameSlot^));
end;

{ -----------------------------------------------------------------------
  CLI argument parsing
  ----------------------------------------------------------------------- }

procedure SplitSuiteSpec(const ASpec: string;
  out ASuite: string; out AMethod: string);
var
  Dot: Integer;
begin
  Dot := Pos('.', ASpec);
  if Dot >= 0 then
  begin
    { Pos is 0-based in Blaise; Copy(s, start, count) where start is
      also 0-based.  Dot is the 0-based index of '.'. }
    ASuite  := Copy(ASpec, 0, Dot);
    AMethod := Copy(ASpec, Dot + 1, Length(ASpec));
  end
  else
  begin
    ASuite  := ASpec;
    AMethod := '';
  end;
end;

{ Trim leading + trailing ASCII whitespace from a string. }
function TrimWS(const S: string): string;
var
  Lo, Hi: Integer;
begin
  Lo := 0;
  Hi := Length(S) - 1;
  while (Lo <= Hi) and ((S[Lo] = ' ') or (S[Lo] = #9)) do
    Lo := Lo + 1;
  while (Hi >= Lo) and ((S[Hi] = ' ') or (S[Hi] = #9)) do
    Hi := Hi - 1;
  if Hi < Lo then
    Result := ''
  else
    Result := Copy(S, Lo, Hi - Lo + 1);
end;

procedure AppendSuiteFilter(AFilters: TList<String>; const ASpec: string);
var
  Start, I: Integer;
  Part:     string;
begin
  if ASpec = '' then Exit;
  Start := 0;
  for I := 0 to Length(ASpec) - 1 do
  begin
    if ASpec[I] = ',' then
    begin
      Part := TrimWS(Copy(ASpec, Start, I - Start));
      if Part <> '' then
        AFilters.Add(Part);
      Start := I + 1;
    end;
  end;
  Part := TrimWS(Copy(ASpec, Start, Length(ASpec) - Start));
  if Part <> '' then
    AFilters.Add(Part);
end;

function MatchesFilters(AFilters: TList<String>;
  const ASuite, AMethod: string): Boolean;
var
  I:        Integer;
  FSuite:   string;
  FMethod:  string;
begin
  if (AFilters = nil) or (AFilters.Count = 0) then
  begin
    Exit(True);
  end;
  for I := 0 to AFilters.Count - 1 do
  begin
    SplitSuiteSpec(AFilters.Get(I), FSuite, FMethod);
    if FSuite <> ASuite then
      Continue;
    if (FMethod = '') or (FMethod = AMethod) then
    begin
      Exit(True);
    end;
  end;
  Result := False;
end;

{ True if any filter in AFilters names ASuite (regardless of whether
  the filter pins a specific method).  Used to decide whether a class
  should be considered for execution at all. }
function FiltersTouchSuite(AFilters: TList<String>;
  const ASuite: string): Boolean;
var
  I:        Integer;
  FSuite:   string;
  FMethod:  string;
begin
  if (AFilters = nil) or (AFilters.Count = 0) then
  begin
    Exit(True);
  end;
  for I := 0 to AFilters.Count - 1 do
  begin
    SplitSuiteSpec(AFilters.Get(I), FSuite, FMethod);
    if FSuite = ASuite then
    begin
      Exit(True);
    end;
  end;
  Result := False;
end;

{ Parse --suite, --verbose and --exclude-category from the process command
  line.  AFilters receives one entry per filter; --suite may appear multiple
  times and each --suite value may be comma-delimited.  Empty list
  means "run everything".  AVerbose is True when --verbose is present.
  AExclCategory is the value of --exclude-category ('' = no exclusion) —
  suites/methods carrying a matching [Category('...')] are skipped.
  AFilters must be created by the caller and is owned by the caller. }
procedure ParseArgs(AFilters: TList<String>; out AVerbose: Boolean;
  out AExclCategory: string);
var
  I:   Integer;
  Arg: string;
begin
  AVerbose      := False;
  AExclCategory := '';
  I := 1;
  while I <= ParamCount() do
  begin
    Arg := ParamStr(I);
    if Arg = '--verbose' then
      AVerbose := True
    else if (Arg = '--suite') and (I < ParamCount()) then
    begin
      I := I + 1;
      AppendSuiteFilter(AFilters, ParamStr(I));
    end
    else if (Arg = '--exclude-category') and (I < ParamCount()) then
    begin
      I := I + 1;
      AExclCategory := ParamStr(I);
    end;
    I := I + 1;
  end;
end;

{ -----------------------------------------------------------------------
  Subprocess-based parallel runner
  ----------------------------------------------------------------------- }

function IsThreadedClass(ATestClass: TTestCaseClass): Boolean;
begin
  Result := HasClassAttribute(ATestClass, ThreadedAttribute);
end;

{ ParseSubprocessOutput: parse --verbose output from a suite subprocess
  into AResult.  Called in the main thread after subprocess completes.

  The output is the verbose outcome lines ("CName.MName ... OUTCOME"), the
  summary line, then the "Failures:" / "Errors:" sections, one entry per
  failed test: "  MName: message".  A message may span SEVERAL lines (a
  compile failure carries the compiler's diagnostics, blank lines and all),
  so an entry runs until the next line that opens an entry for a test the
  outcome lines reported as failed, or until the next section.  Ending the
  section at the first unindented line instead dropped every later failure
  of the suite from both the list and the count. }
procedure ParseSubprocessOutput(const AOutput: string; AResult: TTestResult);
var
  Lines:   TStringList;
  Failed:  TSet<string>;
  I:       Integer;
  Line:    string;
  InFail:  Boolean;
  InErr:   Boolean;
  Pending: Boolean;
  PendErr: Boolean;
  P:       Integer;
  MsgName: string;
  MsgBody: string;

  procedure FlushPending();
  begin
    if not Pending then Exit;
    if PendErr then
      AResult.AddError(MsgName, MsgBody)
    else
      AResult.AddFailure(MsgName, MsgBody);
    Pending := False;
  end;

begin
  Lines := TStringList.Create();
  Failed := TSet<string>.Create();
  try
    Lines.Text := AOutput;
    InFail := False;
    InErr := False;
    Pending := False;
    PendErr := False;
    MsgName := '';
    MsgBody := '';
    for I := 0 to Lines.Count - 1 do
    begin
      Line := Lines.Strings[I];
      if Line = 'Failures:' then
      begin
        FlushPending();
        InFail := True; InErr := False;
        Continue
      end;
      if Line = 'Errors:' then
      begin
        FlushPending();
        InErr := True; InFail := False;
        Continue
      end;
      if InFail or InErr then
      begin
        { "  MethodName: message" opens an entry -- but only for a name the
          outcome lines reported as failed; anything else is a continuation
          line of the current message }
        P := Pos(': ', Line);
        if (Length(Line) > 2) and (Copy(Line, 0, 2) = '  ') and (P > 2) and
           Failed.Contains(Copy(Line, 2, P - 2)) then
        begin
          FlushPending();
          MsgName := Copy(Line, 2, P - 2);
          MsgBody := Copy(Line, P + 2, Length(Line));
          PendErr := InErr;
          Pending := True;
        end
        else if Pending then
          MsgBody := MsgBody + #10 + Line;
        Continue;
      end;
      { Verbose outcome line: "CName.MName ... OUTCOME" }
      if Pos(' ... ', Line) >= 0 then
      begin
        AResult.StartTest('', '');
        if (Pos(' ... FAIL', Line) >= 0) or (Pos(' ... ERROR', Line) >= 0) then
        begin
          AResult.EndTest('FAIL');
          { remember the method part for the detail sections }
          P := Pos(' ... ', Line);
          MsgName := Copy(Line, 0, P);
          while Pos('.', MsgName) >= 0 do
            MsgName := Copy(MsgName, Pos('.', MsgName) + 1, Length(MsgName));
          Failed.Include(MsgName);
        end
        else if Pos(' ... IGNORED', Line) >= 0 then
          AResult.EndTest('IGNORED')
        else
          AResult.EndTest('OK');
      end;
    end;
    FlushPending();
  finally
    Failed.Free();
    Lines.Free();
  end;
end;

{ -----------------------------------------------------------------------
  Test execution
  ----------------------------------------------------------------------- }

{ Run tests with optional class/method filtering and verbosity.
  Pass nil or an empty AFilters list to run every registered test.

  [Threaded] suites are dispatched as subprocesses and launched in
  parallel while non-threaded suites run in-process.  After in-process
  tests finish, remaining subprocess output is collected.
  When --suite is given, the named suite runs directly (no subprocess). }
function RunFilteredTests(AFilters: TList<String>; AVerbose: Boolean;
  const AExclCategory: string): TTestResult;
var
  ClsIdx:    Integer;
  Cls:       TTestCaseClass;
  CName:     string;
  MethCnt:   Integer;
  MethIdx:   Integer;
  MethName:  string;
  Inst:      TTestCase;
  Procs:     array[0..63] of TProcess;
  ProcNames: array[0..63] of string;
  ProcCount: Integer;
  Proc:      TProcess;
  Output:    string;
  Chunk:     string;
  SubResult: TTestResult;
  I:         Integer;
  HasFilter: Boolean;
  ExitCode:  Integer;
  HasSummary: Boolean;
  Attr:      TObject;
  RepCount:  Integer;
  Rep:       Integer;
  AttrIdx:   Integer;
  AttrCnt:   Integer;
  CaseTotal: Integer;
  Sig:       string;
begin
  Result := TTestResult.Create();
  Result.Verbose := AVerbose;
  ProcCount := 0;
  HasFilter := (AFilters <> nil) and (AFilters.Count > 0);
  for ClsIdx := 0 to GetRegisteredTestCount() - 1 do
  begin
    Cls   := GetRegisteredTest(ClsIdx);
    CName := TestClassName(Cls);
    if not FiltersTouchSuite(AFilters, CName) then
      Continue;
    { --exclude-category at class level: skip the whole suite. }
    if (AExclCategory <> '') then
    begin
      Attr := GetClassAttribute(Cls, CategoryAttribute);
      if (Attr <> nil) and SameText(CategoryAttribute(Attr).Name, AExclCategory) then
        Continue;
    end;
    if not HasFilter and IsThreadedClass(Cls) and (ProcCount < 64) then
    begin
      Proc := TProcess.Create(nil);
      Proc.Executable := ParamStr(0);
      Proc.Parameters.Add('--suite');
      Proc.Parameters.Add(CName);
      Proc.Parameters.Add('--verbose');
      if AExclCategory <> '' then
      begin
        Proc.Parameters.Add('--exclude-category');
        Proc.Parameters.Add(AExclCategory);
      end;
      Proc.Execute();
      Procs[ProcCount]     := Proc;
      ProcNames[ProcCount] := CName;
      ProcCount := ProcCount + 1;
    end
    else
    begin
      MethCnt := PublishedMethodCount(Cls);
      for MethIdx := 0 to MethCnt - 1 do
      begin
        MethName := PublishedMethodName(Cls, MethIdx);
        if MethName = '' then Continue;
        if not MatchesFilters(AFilters, CName, MethName) then
          Continue;
        { --exclude-category at method level. }
        if (AExclCategory <> '') and
           MethodInCategory(Cls, MethName, AExclCategory) then
          Continue;
        { [Ignore('reason')] — record as ignored without running. }
        Attr := GetMethodAttribute(Cls, MethName, IgnoreAttribute);
        if Attr <> nil then
        begin
          Result.StartTest(CName, MethName);
          Result.AddIgnored(MethName, IgnoreAttribute(Attr).Reason);
          Result.EndTest('IGNORED');
          Continue;
        end;
        { [Retry(N)] runs every case N times (flake hunting). }
        RepCount := 1;
        Attr := GetMethodAttribute(Cls, MethName, RetryAttribute);
        if Attr <> nil then
          RepCount := RetryAttribute(Attr).Count;
        if RepCount < 1 then RepCount := 1;
        Sig := PublishedMethodSig(Cls, MethIdx);
        { [TestCase('name', 'args')] — one fixture instance and one result
          entry per case, reported as 'Method[name]'.  The method's typed
          parameters are supplied by TTestCase.RunTest's sig-driven
          dispatch (see MethodParamSig in the codegen). }
        CaseTotal := 0;
        AttrCnt := MethodAttributeCount(Cls, MethName);
        for AttrIdx := 0 to AttrCnt - 1 do
        begin
          Attr := GetMethodAttributeAt(Cls, MethName, AttrIdx);
          if not (Attr is TestCaseAttribute) then Continue;
          CaseTotal := CaseTotal + 1;
          for Rep := 1 to RepCount do
          begin
            Inst := Cls.Create(MethName);
            Inst.SetClassName(CName);
            Inst.SetCase(TestCaseAttribute(Attr).Name,
                         TestCaseAttribute(Attr).Args, Sig);
            Inst.Run(Result);
          end;
        end;
        if CaseTotal = 0 then
        begin
          { A parameterised method without [TestCase] data cannot be
            dispatched — surface it loudly instead of calling it with
            garbage registers. }
          if Sig <> '' then
          begin
            Result.StartTest(CName, MethName);
            Result.AddError(MethName,
              'published method has parameters — supply them with ' +
              '[TestCase(''name'', ''args'')] attributes');
            Result.EndTest('ERROR');
            Continue;
          end;
          for Rep := 1 to RepCount do
          begin
            Inst := Cls.Create(MethName);
            Inst.SetClassName(CName);
            Inst.Run(Result);
          end;
        end;
      end;
    end;
  end;
  for I := 0 to ProcCount - 1 do
  begin
    Proc := Procs[I];
    Output := '';
    repeat
      Chunk  := Proc.ReadOutput();
      Output := Output + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    ExitCode := Proc.ExitCode;
    SubResult := TTestResult.Create();
    ParseSubprocessOutput(Output, SubResult);
    Result.MergeFrom(SubResult);
    { Crash / truncation guard.  A healthy suite subprocess always ends with a
      summary line ("OK (...)" or "FAIL (...)").  If that is missing the process
      was killed (e.g. SIGSEGV) or died mid-suite, so its parsed test count is
      silently short — exactly the failure mode that lets a crash masquerade as
      a green run.  Record it as a loud error so RunAll exits non-zero and the
      crash is named under "Errors:".  ProcessExitCode maps a signal death to 1
      and a clean exit to its real code, so a missing summary is the reliable
      signal regardless of exit code. }
    HasSummary := (Pos('OK (', Output) >= 0) or (Pos('FAIL (', Output) >= 0);
    if not HasSummary then
      Result.AddError(ProcNames[I],
        'suite subprocess crashed or was killed before finishing (no summary' +
        ' line; exit code ' + IntToStr(ExitCode) +
        ') — its test count is incomplete')
    else if ExitCode > 1 then
      { Exit > 1 with a summary present is unexpected (RunAll returns 0 or 1);
        surface it rather than trust the partial parse. }
      Result.AddError(ProcNames[I],
        'suite subprocess exited abnormally (code ' + IntToStr(ExitCode) + ')');
    if AVerbose then
      Write(Output);
  end;
end;

function RunRegisteredTests: TTestResult;
begin
  Result := RunFilteredTests(nil, False, '');
end;

{ -----------------------------------------------------------------------
  Reporting
  ----------------------------------------------------------------------- }

procedure PrintSummary(AResult: TTestResult);
var
  I:     Integer;
  Fails: TList<String>;
  Errs:  TList<String>;
  Line:  string;
begin
  WriteLn(AResult.Summary());

  if AResult.NumberOfFailures > 0 then
  begin
    WriteLn('Failures:');
    Fails := AResult.Failures;
    I     := 0;
    while I < AResult.NumberOfFailures do
    begin
      Line := Fails.Get(I);
      WriteLn('  ' + Line);
      I := I + 1
    end;
  end;

  if AResult.NumberOfErrors > 0 then
  begin
    WriteLn('Errors:');
    Errs := AResult.Errors;
    I    := 0;
    while I < AResult.NumberOfErrors do
    begin
      Line := Errs.Get(I);
      WriteLn('  ' + Line);
      I := I + 1
    end;
  end;
end;

function RunAll: Integer;
var
  R:        TTestResult;
  Filters:  TList<String>;
  Verbose:  Boolean;
  ExclCat:  string;
begin
  Filters := TList<String>.Create();
  ParseArgs(Filters, Verbose, ExclCat);
  R := RunFilteredTests(Filters, Verbose, ExclCat);
  PrintSummary(R);
  if (R.NumberOfFailures = 0) and (R.NumberOfErrors = 0) then
    Result := 0
  else
    Result := 1;
end;

end.
