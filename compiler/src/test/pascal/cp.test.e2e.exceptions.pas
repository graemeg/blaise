{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.exceptions;

{ E2E tests for try/finally, try/except, raise, and typed exception handlers. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EExceptionTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Regression for the alloc16-32 exception-frame bug:
      a bare try/finally with no locals, virtuals, or RTL use. }
    procedure TestRun_BareTryFinally;
    { A class declared in a UNIT must reach the one TObject. }
    procedure TestRun_OnTObject_CatchesUnitDeclaredException;

    { Locals live in the stack frame around the exception frame.
      If the exception frame is undersized, setjmp clobbers them. }
    procedure TestRun_TryFinally_PreservesLocals;

    { Exception frame must not corrupt caller state when nested. }
    procedure TestRun_NestedTryFinally;

    { Virtual dispatch in expression position inside try/finally. }
    procedure TestRun_VirtualDispatchInsideTryFinally;

    { Non-local exit (Exit/Break) must run intervening finally bodies. }
    procedure TestRun_ExitThroughFinally;
    procedure TestRun_ExitValueThroughFinally;
    procedure TestRun_ExitThroughNestedFinally;
    procedure TestRun_BreakThroughFinally;

    { Typed except handlers }
    procedure TestRun_TypedExcept_CorrectHandlerMatched;
    procedure TestRun_TypedExcept_SubclassMatchesParentHandler;
    procedure TestRun_TypedExcept_UnmatchedReraises;
    procedure TestRun_TypedExcept_BareRaisePropagatesToOuter;
    procedure TestRun_TypedExcept_ElseBodyRunsWhenNoMatch;

    { String variable mutated in finally must be visible after re-raise. }
    procedure TestRun_FinallyStringMutation_SurvivesReraise;

    { Exit inside the second try block of a function must pop its exc frame;
      a later raise must still dispatch correctly (stale-frame regression). }
    procedure TestRun_ExitInSecondTry_LaterRaiseStillWorks;

    { The div/mod zero guard (emitted when SysUtils is in scope) must not
      disturb normal division.  Catchable-EDivByZero behaviour needs the
      stdlib loaded + linked, which the in-process harness cannot do; that
      is covered by the shell-out test in cp.test.cli.pas. }
    { A for-loop INSIDE a finally body is emitted twice (normal + exception
      path).  Both emissions must reuse the same hidden __for_end slot, and
      the loop must run correctly when reached via the exception path. }
    procedure TestRun_ForLoopInFinally_BothPaths;

    procedure TestRun_DivNonZero_StillWorks;

    { BUG-046: Exception.CreateFmt(fmt, [args]) with no declared CreateFmt
      method must desugar to Create(Format(fmt, [args])) — before the fix
      the args were silently dropped and Message came back empty. }
    procedure TestRun_CreateFmt_FormatsMessage;
  end;

implementation

procedure TE2EExceptionTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-exceptions');
end;

const
  LE = #10;

  SrcBareTryFinally = '''
    program P;
    begin
      try
        WriteLn('in_try')
      finally
        WriteLn('in_finally')
      end
    end.
    ''';

  SrcPreservesLocals = '''
    program P;
    var A, B, C: Integer;
    begin
      A := 11;
      B := 22;
      C := 33;
      try
        WriteLn(A);
        WriteLn(B);
        WriteLn(C)
      finally
        WriteLn(A + B + C)
      end
    end.
    ''';

  SrcNestedTryFinally = '''
    program P;
    begin
      try
        try
          WriteLn('inner_try')
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end.
    ''';

  { Exit inside a try/finally must run the finally body before leaving. }
  SrcExitThroughFinally = '''
    program P;
    procedure Run;
    begin
      try
        WriteLn('in_try');
        Exit;
        WriteLn('unreached')
      finally
        WriteLn('in_finally')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

  { Exit(X) from inside a try/finally must assign the result, run the finally
    body, then return the value to the caller.  Guards the refactor that
    replaces the 'Result := X; Exit;' workaround with 'Exit(X)' in source
    that sits inside try/finally. }
  SrcExitValueThroughFinally = '''
    program P;
    function Pick(b: Boolean): Integer;
    begin
      Result := -1;
      try
        if b then Exit(42);
        WriteLn('unreached')
      finally
        WriteLn('in_finally')
      end;
      Result := 7
    end;
    begin
      WriteLn(Pick(True));
      WriteLn(Pick(False))
    end.
    ''';

  { Exit nested two levels deep must run both finally bodies, innermost first. }
  SrcExitThroughNestedFinally = '''
    program P;
    procedure Run;
    begin
      try
        try
          Exit
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

  { Break out of a loop from inside a try/finally must run the finally body. }
  SrcBreakThroughFinally = '''
    program P;
    var I: Integer;
    begin
      for I := 0 to 3 do
      begin
        try
          if I = 2 then Break;
          WriteLn('iter')
        finally
          WriteLn('fin')
        end
      end;
      WriteLn('done')
    end.
    ''';

  { A for-loop in a finally body must run on BOTH exit paths.  DoIt(False)
    exits the try normally; DoIt(True) raises, so the finally's loop runs on
    the EXCEPTION path (its second emission).  Both sum 0+1+2 = 3.  With the
    slot-reuse bug the exception-path loop stored to an unregistered hidden
    bound slot (codegen error) — this pins the fix. }
  SrcForLoopInFinally = '''
    program P;
    type Exception = class FMessage: string; end;
    procedure DoIt(Boom: Boolean);
    var Acc, I: Integer;
    begin
      Acc := 0;
      try
        if Boom then raise Exception.Create()
      finally
        for I := 0 to 2 do
          Acc := Acc + I;
        WriteLn(Acc)
      end
    end;
    begin
      DoIt(False);
      try
        DoIt(True)
      except
        on E: Exception do WriteLn('caught')
      end
    end.
    ''';

  SrcVirtualDispatchInTry = '''
    program P;
    type
      TNode = class
        function GetTag: Integer; virtual;
      end;
      TMarkedNode = class(TNode)
        function GetTag: Integer; override;
      end;
    function TNode.GetTag: Integer;
    begin Result := 0 end;
    function TMarkedNode.GetTag: Integer;
    begin Result := 1 end;
    var N: TNode; T: Integer;
    begin
      N := TMarkedNode.Create();
      try
        T := N.GetTag();
        WriteLn(T)
      finally
        N.Free()
      end
    end.
    ''';

  { Non-zero divisor: the SysUtils-gated div/mod zero guard must not disturb
    normal division on either backend. }
  SrcDivNonZeroStillWorks = '''
    program P;
    uses SysUtils;
    var a, b: Integer;
    begin
      a := 20; b := 4;
      WriteLn(a div b);
      WriteLn(a mod 7)
    end.
    ''';

  { BUG-046: CreateFmt desugars to Create(Format(...)); the message must
    carry the formatted text, not be dropped.  Exception declares Create
    (string) but NOT CreateFmt — the desugar must synthesize the Format
    call and bind it to Create. }
  SrcCreateFmtFormatsMessage = '''
    program P;
    type
      Exception = class
        FMessage: string;
        constructor Create(AMessage: string);
        property Message: string read FMessage;
      end;
      EFoo = class(Exception) end;
    constructor Exception.Create(AMessage: string);
    begin
      Self.FMessage := AMessage
    end;
    begin
      try
        raise EFoo.CreateFmt('code %d msg %s', [42, 'boom'])
      except
        on E: Exception do WriteLn(E.Message)
      end
    end.
    ''';

  SrcExcBase =
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            property Message: string read FMessage;
          end;
          EFoo = class(Exception) end;
          EBar = class(EFoo) end;
        ''';

  SrcTypedExceptCorrect =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EFoo do X := 42;
            on E: Exception do X := 1
          end;
          WriteLn(X)
        end.
        ''';

  SrcTypedExceptSubclass =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EBar.Create()
          except
            on E: EFoo do X := 7
          end;
          WriteLn(X)
        end.
        ''';

  SrcTypedExceptElseRun =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EBar do X := 9
            else X := 5
          end;
          WriteLn(X)
        end.
        ''';

  SrcTypedExceptBareRaise =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            try
              raise EFoo.Create()
            except
              on E: EFoo do
              begin
                X := 1;
                raise
              end
            end
          except
            on E: EFoo do X := 2
          end;
          WriteLn(X)
        end.
        ''';

  SrcTypedExceptUnmatched =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            try
              raise EFoo.Create()
            except
              on E: EBar do X := 9
            end
          except
            on E: EFoo do X := 3
          end;
          WriteLn(X)
        end.
        ''';

  SrcFinallyStringMutationSurvives =
    SrcExcBase +
    '''
        var S: string;
        begin
          S := '';
          try
            try
              S := S + 'A,';
              raise EFoo.Create()
            finally
              S := S + 'F,'
            end
          except
            on E: EFoo do
              S := S + 'H,'
          end;
          WriteLn(S)
        end.
        ''';

procedure TE2EExceptionTests.TestRun_BareTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcBareTryFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'in_try' + LE + 'in_finally' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_TryFinally_PreservesLocals;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcPreservesLocals, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('locals preserved',
    '11' + LE + '22' + LE + '33' + LE + '66' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_NestedTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNestedTryFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'inner_try' + LE + 'inner_fin' + LE + 'outer_fin' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_ExitThroughFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExitThroughFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  { Exit runs the finally body, then control returns to the caller. }
  AssertEquals('stdout',
    'in_try' + LE + 'in_finally' + LE + 'after' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_ExitValueThroughFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExitValueThroughFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  { True: Exit(42) sets Result, runs finally, returns 42.
    False: falls through, runs finally, then Result := 7. }
  AssertEquals('stdout',
    'in_finally' + LE + '42' + LE +
    'unreached' + LE + 'in_finally' + LE + '7' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_ExitThroughNestedFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExitThroughNestedFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  { Both finally bodies run, innermost first, before the caller resumes. }
  AssertEquals('stdout',
    'inner_fin' + LE + 'outer_fin' + LE + 'after' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_BreakThroughFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcBreakThroughFinally, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  { Iterations 0,1 print iter+fin; iteration 2 breaks but still runs fin. }
  AssertEquals('stdout',
    'iter' + LE + 'fin' + LE + 'iter' + LE + 'fin' + LE + 'fin' + LE +
    'done' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_VirtualDispatchInsideTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVirtualDispatchInTry, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout (virtual -> marked -> 1)', '1' + LE, Output);
end;

procedure TE2EExceptionTests.TestRun_TypedExcept_CorrectHandlerMatched;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptCorrect, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('EFoo handler ran', '42', Trim(Output));
end;

procedure TE2EExceptionTests.TestRun_TypedExcept_SubclassMatchesParentHandler;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptSubclass, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('EBar matches EFoo handler', '7', Trim(Output));
end;

procedure TE2EExceptionTests.TestRun_TypedExcept_UnmatchedReraises;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptUnmatched, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('unmatched inner re-raises to outer', '3', Trim(Output));
end;

procedure TE2EExceptionTests.TestRun_TypedExcept_BareRaisePropagatesToOuter;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptBareRaise, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('bare raise propagated to outer handler', '2', Trim(Output));
end;

procedure TE2EExceptionTests.TestRun_TypedExcept_ElseBodyRunsWhenNoMatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptElseRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('else body ran when no handler matched', '5', Trim(Output));
end;

procedure TE2EExceptionTests.TestRun_FinallyStringMutation_SurvivesReraise;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFinallyStringMutationSurvives, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('string mutations in finally survive re-raise', 'A,F,H,', Trim(Output));
end;

const
  SrcExitInSecondTry = '''
    program P;
    type EBoom = class end;

    function F(n: Integer): Integer;
    begin
      Result := 0;
      try
        if n = 0 then
        begin
          Exit(100);
        end;
      except
      end;
      try
        repeat
          if n > 2 then
          begin
            Exit(n * 10);
          end;
          n := n + 1;
        until False;
      except
      end;
    end;

    var x: Integer;
    begin
      x := F(0);
      writeln(x);
      x := F(5);
      writeln(x);
      try
        raise EBoom.Create();
      except
        on E: EBoom do writeln('caught');
      end;
      writeln('done');
    end.
    ''';

procedure TE2EExceptionTests.TestRun_OnTObject_CatchesUnitDeclaredException;
const
  { Exception is declared in SysUtils, so its typeinfo's parent link is a
    reference from SysUtils' own object.  The macOS internal linker bound
    that reference to SysUtils' private weak copy of _typeinfo_TObject
    instead of the one copy every other unit uses, so the parent walk never
    met the TObject the handler compared against: `on E: TObject` matched
    nothing and the program aborted.  A program-level class was unaffected,
    which is why the second check is the one that discriminates. }
  Src = '''
    program P;
    uses SysUtils;
    type
      TMine = class end;
      ESem = class(Exception) end;
    var
      Caught: Boolean;
      M: TMine;
      E: Exception;
    begin
      Caught := False;
      try
        raise ESem.Create('x');
      except
        on X: TObject do Caught := True;
      end;
      WriteLn(Caught);
      M := TMine.Create();
      E := ESem.Create('y');
      WriteLn(M is TObject, ' ', E is TObject, ' ', E is Exception);
      M.Free();
      E.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE + 'True True True' + LE, 0);
end;

procedure TE2EExceptionTests.TestRun_ExitInSecondTry_LaterRaiseStillWorks;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitInSecondTry,
    '100' + LE + '50' + LE + 'caught' + LE + 'done' + LE, 0);
end;

procedure TE2EExceptionTests.TestRun_ForLoopInFinally_BothPaths;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { normal-path loop prints 3; exception-path loop prints 3, then 'caught' }
  AssertRunsOnAll(SrcForLoopInFinally,
    '3' + LE + '3' + LE + 'caught' + LE, 0);
end;

procedure TE2EExceptionTests.TestRun_DivNonZero_StillWorks;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDivNonZeroStillWorks, '5' + LE + '6' + LE, 0);
end;

procedure TE2EExceptionTests.TestRun_CreateFmt_FormatsMessage;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCreateFmtFormatsMessage, 'code 42 msg boom' + LE, 0);
end;

initialization
  RegisterTest(TE2EExceptionTests);

end.
