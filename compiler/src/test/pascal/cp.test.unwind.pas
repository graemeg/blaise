{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
{
  Exception unwind tables (docs/exception-unwind-cleanup-design.adoc).

  TUnwindAsmTests: the block every object carries, on both ISAs, and the
  invariant that the tables change no instruction (the routine text with and
  without --no-unwind-tables is identical once the unwind-only lines are
  removed).  TUnwindE2ETests: the runtime walk, on the host ISA.
}
unit cp.test.unwind;

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness, cp.test.e2e.base,
  uUnwindFacts;

type
  TUnwindAsmTests = class(TTestCase)
  private
    procedure CheckShape(const AAsm, ALocalPrefix, AWord, AZero: string);
    procedure CheckIdentity(const ATarget: string);
  published
    { one block per object: the magic, a routine record per routine, its
      labels in the right places }
    procedure TestBlock_ShapeAndLabels_Arm64;
    procedure TestBlock_ShapeAndLabels_X86_64;
    { the tables add data and labels, never an instruction }
    procedure TestTextIdentity_Arm64;
    procedure TestTextIdentity_X86_64;
  end;

  TUnwindE2ETests = class(TE2ETestCase)
  public
    procedure SetUp; override;
  published
    { a raise walks every Blaise frame up to the handler's, through deep
      recursion too, and is still caught }
    procedure TestRun_WalkFindsEveryFrame;
    { a frame an exception passes releases its strings, class references,
      interfaces, dynamic arrays, closure environment and [Weak] slots --
      by-value parameters too -- whether it has no try, a finally, an
      unmatched handler or re-raises; the frame that catches keeps its own }
    procedure TestDebug_ScalarLocals_ReleasedOnUnwind;
    { the same inside a thread and inside a fibre, each with its own
      exception chain }
    procedure TestDebug_RaiseInThread_ReleasesLocals;
    procedure TestDebug_RaiseInFiber_ReleasesLocals;
    { records with managed fields (nested, with a [Weak] field) and static
      arrays of managed elements, as locals and as by-value parameters }
    procedure TestDebug_AggregateLocals_ReleasedOnUnwind;
    { a function's own managed Result -- string, class, dynamic array,
      'reference to' closure, managed record -- is released when
      the function raises after assigning it; the caller's variable keeps its
      old value; an 'of object' result owns nothing }
    procedure TestDebug_ManagedResult_ReleasedOnUnwind;
    { owned string and class temporaries passed to a call that raises are
      released, whether the raise leaves the caller or is caught in it, with
      nested calls among the arguments; a result moved into a variable is
      released once }
    procedure TestDebug_CallArgTemporaries_ReleasedOnUnwind;
    { a deferred-release base (a field read off an owned temporary) is
      released by the walk; one whose statement spans a try that catches is
      left to that statement }
    procedure TestDebug_DeferredBases_ReleasedOnUnwind;
    { a raise statement's own deferred base is not released under the
      exception it owns (BUG-049: it is left to leak) }
    procedure TestRun_RaiseOperandBase_NotFreedUnderIt;
    { an owned string operand -- an rc = 1 call result or an rc = 0 concat --
      held while the other operand of + or a comparison raises }
    procedure TestDebug_StringOperands_ReleasedOnUnwind;
    { the main program's own call-argument and operand temporaries: main is
      a routine to the tables too }
    procedure TestDebug_MainTemporaries_ReleasedOnUnwind;
    { a constructor that raises releases its new instance, which runs the
      destructor on the partly built object (D2): a plain, a virtual (through
      a metaclass) and a nested constructor call, and one that registered
      Self elsewhere before it raised }
    procedure TestDebug_RaisingConstructor_ReleasesInstance;
    { a managed record built by a call for an argument (TakeRec(MkRec())) is
      released when a later argument raises or the callee does: const and
      by-value parameters, a large and a small (register-returned) record,
      a method callee }
    procedure TestDebug_RecordCallArgs_ReleasedOnUnwind;
    { an owned receiver -- an interface, class or managed record returned by
      a call -- is released when its call's argument or the call raises:
      scalar, interface and record results, statement and expression }
    procedure TestDebug_OwnedReceivers_ReleasedOnUnwind;
    { a try/except in a unit's initialization or finalization section:
      named and unnamed handlers bind their exception (arm64 had no slot for
      it -- an internal error), and the temporaries a caught raise passes
      are released }
    procedure TestDebug_UnitSectionTryExcept;
    { the main program's deferred-release bases and record scratches, which
      x86-64 keeps in .bss (absolute ranges): released when a raise is
      caught in main }
    procedure TestDebug_MainDeferredBases_ReleasedOnUnwind;
    { a destructor that raises while the walk releases: the new exception
      replaces the in-flight one, which is released (D1); the walk carries
      on through the field-cleanup function and the aggregate hook (each
      field released once, zeroed before its release); a destructor that
      catches its own exception leaves the original in flight }
    procedure TestDebug_RaisingDestructor_DuringUnwind;
  end;

implementation

const
  ShapeSrc =
    '''
    program Shape;
    procedure Work;
    var S: string;
    begin
      S := 'x';
      WriteLn(S);
    end;
    begin
      Work();
    end.
    ''';

  { a mix of frames, temporaries, try blocks and closures }
  IdentitySrc =
    '''
    program Ident;
    type
      TErr = class
        Msg: string;
      end;
      TFn = reference to function(X: Int): Int;
      TRec = record A: string; B: Int; end;
      TObj = class
        Name: string;
        function Twice(X: Int): Int;
      end;
    function TObj.Twice(X: Int): Int;
    begin
      Result := X * 2;
    end;
    function MkStr(N: Int): string;
    begin
      Result := 'n' + Chr(N + 48) + '!';
    end;
    function Adder(K: Int): TFn;
    begin
      Result := function(X: Int): Int begin Result := X + K end;
    end;
    procedure Work(const A: string; B: string; R: TRec);
    var
      O: TObj;
      L: array of string;
      F: TFn;
      S: string;
    begin
      O := TObj.Create();
      SetLength(L, 2);
      L[0] := MkStr(1) + MkStr(2);
      F := Adder(3);
      try
        S := A + B + R.A + MkStr(F(O.Twice(4)));
        if Length(S) > 100 then raise TErr.Create();
      except
        on E: TErr do S := E.Msg;
      end;
      WriteLn(S, L[0]);
    end;
    var R: TRec;
    begin
      R.A := 'r';
      Work('a', 'b', R);
    end.
    ''';

function Lines(const S: string): TStringList;
begin
  Result := TStringList.Create();
  Result.Text := S;
end;

function IndexOfPrefix(L: TStringList; const APrefix: string; AFrom: Int): Int;
var
  I: Int;
begin
  for I := AFrom to L.Count - 1 do
    if Pos(APrefix, L.Strings[I]) = 0 then Exit(I);
  Result := -1;
end;

function IndexOfSub(L: TStringList; const ASub: string; AFrom: Int): Int;
var
  I: Int;
begin
  for I := AFrom to L.Count - 1 do
    if Pos(ASub, L.Strings[I]) >= 0 then Exit(I);
  Result := -1;
end;

{ The assembly with every unwind-only line removed: the code labels, the
  object's tail (the aggregate release hooks and the end-of-text label), the
  block and the _UnwindInit call in _main. }
function StripUnwind(const AAsm: string): string;
var
  L, R: TStringList;
  I, Phase: Int;
  S: string;
begin
  L := Lines(AAsm);
  R := TStringList.Create();
  try
    { Phase 1: the object's unwind-only tail -- the .text switch, the
      aggregate hooks and the end-of-text label -- up to the block's section
      directive; phase 2: the block, up to the .text switch that ends it }
    Phase := 0;
    for I := 0 to L.Count - 1 do
    begin
      S := L.Strings[I];
      if Phase = 1 then
      begin
        if (Pos('.section', S) >= 0) and ((Pos('__blaise_unw', S) >= 0) or
           (Pos('blaise_unwind', S) >= 0)) then
          Phase := 2;
        Continue;
      end;
      if Phase = 2 then
      begin
        if Trim(S) = '.text' then Phase := 0;
        Continue;
      end;
      if (Trim(S) = '.text') and (I + 1 < L.Count) and
         ((Pos('unw_agg', L.Strings[I + 1]) >= 0) or
          (Pos('unw_hi', L.Strings[I + 1]) >= 0)) then
      begin
        Phase := 1;
        Continue;
      end;
      if (Pos('.section', S) >= 0) and ((Pos('__blaise_unw', S) >= 0) or
         (Pos('blaise_unwind', S) >= 0)) then
      begin
        { a block with no routine has no tail before it }
        Phase := 2;
        Continue;
      end;
      { the code labels, and the _UnwindInit call with its two bound
        arguments (named after the section) }
      if (Pos('unw_', S) >= 0) or (Pos('_UnwindInit', S) >= 0) or
         (Pos('blaise_unw', S) >= 0) then Continue;
      R.Add(S);
    end;
    Result := R.Text;
  finally
    R.Free();
    L.Free();
  end;
end;

procedure TUnwindAsmTests.CheckShape(const AAsm, ALocalPrefix, AWord, AZero: string);
var
  L: TStringList;
  Sym, Start, Cov, Sect: Int;
begin
  L := Lines(AAsm);
  try
    Sect := IndexOfSub(L, '.section', 0);
    while (Sect >= 0) and (IndexOfSub(L, 'unw', Sect) <> Sect) do
      Sect := IndexOfSub(L, '.section', Sect + 1);
    AssertTrue('an unwind section directive', Sect >= 0);
    AssertTrue('the block starts with the magic',
      IndexOfSub(L, AWord + ' ' + IntToStr(UNW_MAGIC), Sect) > Sect);
    Sym := IndexOfSub(L, 'Work:', 0);
    AssertTrue('routine symbol', Sym >= 0);
    Start := IndexOfPrefix(L, ALocalPrefix + 'unw_s', Sym);
    AssertEquals('the routine start label follows the symbol', Sym + 1, Start);
    Cov := IndexOfPrefix(L, ALocalPrefix + 'unw_c', Start);
    AssertTrue('a coverage label', Cov > Start);
    AssertTrue('the local is zeroed before coverage starts',
      (IndexOfSub(L, AZero, Start) > Start) and
      (IndexOfSub(L, AZero, Start) < Cov));
    AssertTrue('coverage starts before the exit label',
      IndexOfSub(L, 'exit', Cov) > Cov);
    AssertTrue('the routine record covers to its exit label',
      IndexOfSub(L, 'exit', Sect) > Sect);
    AssertTrue('a routine end label after the symbol',
      IndexOfPrefix(L, ALocalPrefix + 'unw_e', Cov) > Cov);
  finally
    L.Free();
  end;
end;

procedure TUnwindAsmTests.TestBlock_ShapeAndLabels_Arm64;
begin
  CheckShape(GenAsm(ShapeSrc, TargetArm64), 'L', '.word', 'xzr');
end;

procedure TUnwindAsmTests.TestBlock_ShapeAndLabels_X86_64;
begin
  CheckShape(GenAsm(ShapeSrc, TargetX86_64), '.L', '.long', '$0,');
end;

procedure TUnwindAsmTests.CheckIdentity(const ATarget: string);
var
  WithTables, Without: string;
begin
  WithTables := GenAsm(IdentitySrc, ATarget);
  GNoUnwindTables := True;
  try
    Without := GenAsm(IdentitySrc, ATarget);
  finally
    GNoUnwindTables := False;
  end;
  AssertTrue('the tables are present', Pos('unw_', WithTables) >= 0);
  AssertTrue('--no-unwind-tables emits none', Pos('unw_', Without) < 0);
  AssertEquals('instructions unchanged', Without, StripUnwind(WithTables));
end;

procedure TUnwindAsmTests.TestTextIdentity_Arm64;
begin
  CheckIdentity(TargetArm64);
end;

procedure TUnwindAsmTests.TestTextIdentity_X86_64;
begin
  CheckIdentity(TargetX86_64);
end;

procedure TUnwindE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-unwind');
end;

procedure TUnwindE2ETests.TestRun_WalkFindsEveryFrame;
begin
  AssertRunsOnAll(
    '''
    program Walk;
    uses SysUtils;
    function _UnwindLastWalk: Int; external name '_UnwindLastWalk';
    procedure P3;
    begin
      raise Exception.Create('deep');
    end;
    { a managed local keeps x86-64 from inlining a one-call body }
    procedure P2;
    var S: string;
    begin
      S := 'p' + Chr(50);
      P3();
      WriteLn(S);
    end;
    procedure P1;
    var S: string;
    begin
      S := 'p' + Chr(49);
      P2();
      WriteLn(S);
    end;
    procedure Recurse(N: Int);
    begin
      if N = 0 then raise Exception.Create('bottom');
      Recurse(N - 1);
    end;
    procedure Local;
    begin
      try
        raise Exception.Create('here');
      except
        on E: Exception do
          WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
    end;
    begin
      try
        P1();
      except
        on E: Exception do WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
      try
        Recurse(1000);
      except
        on E: Exception do WriteLn(E.Message, ' ', _UnwindLastWalk());
      end;
      Local();
    end.
    ''',
    { every Blaise frame from the raise to the handler's, that one
      included: P3, P2, P1 and main; 1001 Recurse frames and main; Local }
    'deep 4' + #10 + 'bottom 1002' + #10 + 'here 1' + #10, 0);
end;

procedure TUnwindE2ETests.TestDebug_ScalarLocals_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwindLocals;
    uses SysUtils;
    type
      TTrack = class
        Name: string;
        constructor Create(const AName: string);
        destructor Destroy; override;
      end;
      ISome = interface
        procedure Hello;
      end;
      TSome = class(ISome)
        procedure Hello;
        destructor Destroy; override;
      end;
      TFn = reference to function: Int;
    var
      Freed: Int;
    constructor TTrack.Create(const AName: string);
    begin
      Name := AName;
    end;
    destructor TTrack.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    procedure TSome.Hello;
    begin
    end;
    destructor TSome.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    procedure Boom;
    begin
      raise Exception.Create('boom');
    end;
    procedure Strs(const C: string; P: string);
    var S: string;
    begin
      S := IntToStr(Length(P)) + C;
      Boom();
    end;
    { the argument is a local, passed borrowed: main's own temporaries (a
      call result, or a global it pins) are step 12 }
    procedure RunStrs;
    var A: string;
    begin
      A := IntToStr(12345);
      Strs('c', A);
    end;
    procedure Objs;
    var
      O: TTrack;
      I: ISome;
      D: array of TTrack;
      [Weak] W: TTrack;
    begin
      O := TTrack.Create('o');
      I := TSome.Create();
      SetLength(D, 2);
      D[0] := TTrack.Create('d0');
      D[1] := TTrack.Create('d1');
      W := O;
      Boom();
    end;
    procedure Closure;
    var
      K: Int;
      O: TTrack;
      F: TFn;
    begin
      K := 7;
      O := TTrack.Create('c');
      F := function: Int begin Result := K + Length(O.Name) end;
      Boom();
    end;
    procedure Mid;
    begin
      Objs();
    end;
    procedure WithFinally;
    var O: TTrack;
    begin
      O := TTrack.Create('f');
      try
        Boom();
      finally
        Write('finally ');
      end;
    end;
    procedure Unmatched;
    var O: TTrack;
    begin
      O := TTrack.Create('u');
      try
        Boom();
      except
        on E: EConvertError do WriteLn('no');
      end;
    end;
    procedure ReRaise;
    var O: TTrack;
    begin
      O := TTrack.Create('r');
      try
        Boom();
      except
        raise;
      end;
    end;
    procedure KeepsOwn;
    var O: TTrack;
    begin
      O := TTrack.Create('k');
      try
        Boom();
      except
        on E: Exception do Write('kept ', O.Name, ' ', Freed, ' ');
      end;
    end;
    procedure Step(const ATag: string);
    begin
      WriteLn(ATag, ' ', Freed);
      Freed := 0;
    end;
    begin
      Freed := 0;
      try RunStrs(); except on E: Exception do Step('strs'); end;
      try Mid(); except on E: Exception do Step('objs'); end;
      try Closure(); except on E: Exception do Step('closure'); end;
      try WithFinally(); except on E: Exception do Step('finally'); end;
      try Unmatched(); except on E: Exception do Step('unmatched'); end;
      try ReRaise(); except on E: Exception do Step('reraise'); end;
      KeepsOwn();
      Step('keepsown');
      WriteLn('done');
    end.
    ''',
    'strs 0' + #10 + 'objs 4' + #10 + 'closure 1' + #10 +
    'finally finally 1' + #10 + 'unmatched 1' + #10 + 'reraise 1' + #10 +
    'kept k 0 keepsown 1' + #10 + 'done');
end;

procedure TUnwindE2ETests.TestDebug_RaiseInThread_ReleasesLocals;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwThread;
    uses SysUtils, Classes;
    type
      TW = class(TThread)
        procedure Execute; override;
      end;
    var Seen: string;
    procedure Deep(const ATag: string);
    var S: string; L: TStringList;
    begin
      S := ATag + IntToStr(Length(ATag));
      L := TStringList.Create();
      L.Add(S);
      raise Exception.Create(S);
    end;
    procedure TW.Execute;
    begin
      try
        Deep('worker');
      except
        on E: Exception do Seen := E.Message;
      end;
    end;
    var T: TW;
    begin
      T := TW.Create(False);
      T.WaitFor();
      T := nil;
      WriteLn(Seen);
    end.
    ''', 'worker6');
end;

procedure TUnwindE2ETests.TestDebug_RaiseInFiber_ReleasesLocals;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwFiber;
    uses SysUtils, Classes, async.fibers.context;
    var
      MainF, F: PFiber;
      Seen: string;
    procedure Deep(N: Int);
    var S: string; L: TStringList;
    begin
      S := 'fib' + IntToStr(N);
      L := TStringList.Create();
      L.Add(S);
      if N = 0 then raise Exception.Create(S);
      Deep(N - 1);
    end;
    procedure Work(AArg: Pointer);
    begin
      try
        Deep(3);
      except
        on E: Exception do Seen := E.Message;
      end;
      FiberSwitch(F, MainF);
    end;
    begin
      MainF := FiberCreateMain();
      F := FiberSpawn(@Work, nil, 0);
      FiberSwitch(MainF, F);
      WriteLn(Seen);
    end.
    ''', 'fib0');
end;

procedure TUnwindE2ETests.TestDebug_AggregateLocals_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwAgg;
    uses SysUtils;
    type
      TTrack = class
        destructor Destroy; override;
      end;
      TInner = record
        S: string;
        O: TTrack;
      end;
      TRec = record
        N: Int;
        Name: string;
        Inner: TInner;
        [Weak] Peer: TTrack;
        Arr: array of string;
      end;
      TStrs = array[0..2] of string;
    var
      Freed: Int;
    destructor TTrack.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    procedure Boom;
    begin
      raise Exception.Create('boom');
    end;
    procedure Locals;
    var
      R: TRec;
      A: TStrs;
      K: TTrack;
    begin
      K := TTrack.Create();
      R.Name := 'n' + IntToStr(1);
      R.Inner.S := 's' + IntToStr(2);
      R.Inner.O := TTrack.Create();
      R.Peer := K;
      SetLength(R.Arr, 2);
      R.Arr[1] := 'a' + IntToStr(3);
      A[0] := 'x' + IntToStr(4);
      A[2] := 'y' + IntToStr(5);
      Boom();
    end;
    procedure Params(R: TRec; A: TStrs);
    begin
      Boom();
    end;
    var
      R: TRec;
      A: TStrs;
    begin
      try Locals(); except on E: Exception do WriteLn('locals ', Freed); end;
      Freed := 0;
      R.Name := 'p' + IntToStr(6);
      R.Inner.O := TTrack.Create();
      A[1] := 'q' + IntToStr(7);
      try Params(R, A); except on E: Exception do WriteLn('params ', Freed); end;
      WriteLn('done');
    end.
    ''', 'locals 2' + #10 + 'params 0' + #10 + 'done');
end;

procedure TUnwindE2ETests.TestDebug_ManagedResult_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwResult;
    uses SysUtils;
    type
      TTrack = class
        destructor Destroy; override;
        procedure Ping;
      end;
      IThing = interface
        procedure Hello;
      end;
      TThing = class(IThing)
        procedure Hello;
        destructor Destroy; override;
      end;
      TFn = reference to function: Int;
      TMeth = procedure of object;
      TRec = record
        S: string;
        O: TTrack;
      end;
      TArr = array of string;
    var
      Freed: Int;
      Keep: TTrack;
    destructor TTrack.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    procedure TTrack.Ping;
    begin
    end;
    procedure TThing.Hello;
    begin
    end;
    destructor TThing.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    procedure Boom;
    begin
      raise Exception.Create('boom');
    end;
    function FStr(): string;
    begin
      Result := 'r' + IntToStr(1);
      Boom();
    end;
    function FObj(): TTrack;
    begin
      Result := TTrack.Create();
      Boom();
    end;
    function FArr(): TArr;
    begin
      SetLength(Result, 2);
      Result[0] := 'a' + IntToStr(2);
      Boom();
    end;
    function FFn(): TFn;
    var K: TTrack;
    begin
      K := TTrack.Create();
      Result := function: Int begin K.Ping(); Result := 1 end;
      K := nil;
      Boom();
    end;
    function FRec(): TRec;
    begin
      Result.S := 's' + IntToStr(3);
      Result.O := TTrack.Create();
      Boom();
    end;
    procedure RunRec;
    var R: TRec;
    begin
      try R := FRec(); except on E: Exception do WriteLn('rec'); end;
    end;
    function FMeth(): TMeth;
    begin
      Result := @Keep.Ping;
      Boom();
    end;
    var
      S: string;
      O: TTrack;
      A: TArr;
      F: TFn;
      M: TMeth;
    begin
      Keep := TTrack.Create();
      S := 'old';
      try S := FStr(); except on E: Exception do WriteLn('str ', S); end;
      try O := FObj(); except on E: Exception do WriteLn('obj ', Freed, ' ', O = nil); end;
      Freed := 0;
      try A := FArr(); except on E: Exception do WriteLn('arr ', Length(A)); end;
      try F := FFn(); except on E: Exception do WriteLn('fn ', Freed); end;
      Freed := 0;
      { x86-64 builds a managed record result in the caller's variable, as
        Delphi does, arm64 in its own frame: either way nothing leaks }
      RunRec();
      Freed := 0;
      try M := FMeth(); except on E: Exception do WriteLn('meth ', Freed); end;
      Keep := nil;
      WriteLn('keep ', Freed);
    end.
    ''',
    'str old' + #10 + 'obj 1 True' + #10 + 'arr 0' + #10 +
    'fn 1' + #10 + 'rec' + #10 + 'meth 0' + #10 + 'keep 1');
end;

procedure TUnwindE2ETests.TestDebug_CallArgTemporaries_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwArgs;
    uses SysUtils;
    type
      TTrack = class
        destructor Destroy; override;
      end;
    var
      Freed: Int;
    destructor TTrack.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    function MkStr(N: Int): string;
    begin
      Result := IntToStr(N) + 'x';
    end;
    function MkObj(): TTrack;
    begin
      Result := TTrack.Create();
    end;
    function Wrap(const A: string): string;
    begin
      Result := '[' + A + ']';
    end;
    procedure Take(const A: string; O: TTrack; const B: string);
    begin
      raise Exception.Create(A + B);
    end;
    procedure Passes;
    var S: string;
    begin
      S := 'p';
      Take(MkStr(1) + S, MkObj(), Wrap(MkStr(2)));
    end;
    procedure Catches;
    begin
      try
        Take(MkStr(3), MkObj(), MkStr(4));
      except
        on E: Exception do Write('caught ', E.Message, ' ', Freed, ' ');
      end;
    end;
    procedure Moved;
    var O: TTrack;
    begin
      O := MkObj();
      Take(MkStr(5), O, MkStr(6));
    end;
    begin
      try Passes(); except on E: Exception do WriteLn('passes ', E.Message, ' ', Freed); end;
      Freed := 0;
      Catches();
      WriteLn(Freed);
      Freed := 0;
      try Moved(); except on E: Exception do WriteLn('moved ', Freed); end;
    end.
    ''',
    'passes 1xp[2x] 1' + #10 + 'caught 3x4x 1 1' + #10 + 'moved 1');
end;

procedure TUnwindE2ETests.TestDebug_DeferredBases_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwPend;
    uses SysUtils, Generics.Collections;
    type
      TTrack = class
        Name: string;
        List: TList<string>;
        constructor Create(const AName: string);
        destructor Destroy; override;
      end;
    var
      Freed: Int;
    constructor TTrack.Create(const AName: string);
    begin
      Name := AName;
      List := TList<string>.Create();
      List.Add('a');
      List.Add('b');
    end;
    destructor TTrack.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    function MkObj(const AName: string): TTrack;
    begin
      Result := TTrack.Create(AName);
    end;
    procedure Take(const S: string);
    begin
      raise Exception.Create(S);
    end;
    procedure FieldArg;
    begin
      Take(MkObj('f').Name);
    end;
    procedure LoopCatches;
    var S: string;
    begin
      for S in MkObj('l').List do
        try
          Take(S);
        except
          on E: Exception do Write(E.Message, ' ');
        end;
    end;
    begin
      try FieldArg(); except on E: Exception do WriteLn('field ', E.Message, ' ', Freed); end;
      Freed := 0;
      LoopCatches();
      WriteLn('loop ', Freed);
    end.
    ''', 'field f 1' + #10 + 'a b loop 1');
end;

procedure TUnwindE2ETests.TestRun_RaiseOperandBase_NotFreedUnderIt;
begin
  { the walk releases no deferred base of a raise statement's own operand:
    the exception it raises is owned through that base (BUG-049) }
  AssertRunsOnAll(
    '''
    program UnwRaiseBase;
    uses SysUtils;
    type
      TFactory = class
        Exc: Exception;
      end;
    function MakeFactory(): TFactory;
    begin
      Result := TFactory.Create();
      Result.Exc := Exception.Create('owned');
    end;
    procedure RaiseField;
    var S: string;
    begin
      S := 'local';
      raise MakeFactory().Exc;
    end;
    begin
      try
        RaiseField();
      except
        on E: Exception do WriteLn('raise ', E.Message, ' ', E.ClassName);
      end;
    end.
    ''', 'raise owned Exception' + #10, 0);
end;

procedure TUnwindE2ETests.TestDebug_StringOperands_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwOperands;
    uses SysUtils;
    function MkStr(N: Int): string;
    begin
      Result := IntToStr(N) + 'x';
    end;
    function Boom(): Int;
    begin
      raise Exception.Create('b');
    end;
    function BoomS(): string;
    begin
      raise Exception.Create('s');
    end;
    procedure Concat;
    var S: string;
    begin
      S := MkStr(1) + IntToStr(Boom());
    end;
    procedure Nested;
    var S: string;
    begin
      S := (MkStr(2) + '-') + BoomS();
    end;
    procedure Compare;
    begin
      if MkStr(3) = BoomS() then WriteLn('eq');
    end;
    procedure Order;
    begin
      if (MkStr(4) + 'y') < BoomS() then WriteLn('lt');
    end;
    begin
      try Concat(); except on E: Exception do WriteLn('concat ', E.Message); end;
      try Nested(); except on E: Exception do WriteLn('nested ', E.Message); end;
      try Compare(); except on E: Exception do WriteLn('compare ', E.Message); end;
      try Order(); except on E: Exception do WriteLn('order ', E.Message); end;
    end.
    ''', 'concat b' + #10 + 'nested s' + #10 + 'compare s' + #10 + 'order s');
end;

procedure TUnwindE2ETests.TestDebug_RaisingConstructor_ReleasesInstance;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwCtor;
    uses SysUtils, Generics.Collections;
    type
      TPart = class
        Name: string;
        constructor Create(const AName: string);
        destructor Destroy; override;
      end;
      TBase = class
        Tag: string;
        Part: TPart;
        constructor Create(AFail: Boolean); virtual;
        destructor Destroy; override;
      end;
      TBaseClass = class of TBase;
      TDerived = class(TBase)
        constructor Create(AFail: Boolean); override;
      end;
      THolder = class
        Inner: TPart;
        constructor Create(AInner: TPart; AFail: Boolean);
        destructor Destroy; override;
      end;
    var
      Freed: Int;
      Registry: TList<TBase>;
    constructor TPart.Create(const AName: string);
    begin
      Name := AName;
    end;
    destructor TPart.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    constructor TBase.Create(AFail: Boolean);
    begin
      Tag := IntToStr(7) + 'tag';
      Part := TPart.Create('p');
      if AFail then raise Exception.Create('base');
    end;
    destructor TBase.Destroy;
    begin
      Freed := Freed + 10;
      inherited Destroy();
    end;
    constructor TDerived.Create(AFail: Boolean);
    begin
      Registry.Add(Self);
      inherited Create(AFail);
    end;
    constructor THolder.Create(AInner: TPart; AFail: Boolean);
    begin
      Inner := AInner;
      if AFail then raise Exception.Create('holder');
    end;
    destructor THolder.Destroy;
    begin
      Freed := Freed + 100;
      inherited Destroy();
    end;
    procedure Plain;
    var B: TBase;
    begin
      B := TBase.Create(True);
      WriteLn('unreached ', B.Tag);
    end;
    procedure Virt(C: TBaseClass);
    var B: TBase;
    begin
      B := C.Create(True);
      WriteLn('unreached ', B.Tag);
    end;
    procedure Nested;
    var H: THolder;
    begin
      H := THolder.Create(TPart.Create(IntToStr(1)), True);
      WriteLn('unreached ', H.Inner.Name);
    end;
    procedure ByValue(C: TBaseClass);
    var B: TBase;
    begin
      B := ClassCreate(C, True);
      WriteLn('unreached ', B.Tag);
    end;
    procedure Caught;
    var B: TBase;
    begin
      try
        B := TBase.Create(True);
      except
        on E: Exception do WriteLn('caught ', E.Message, ' ', B = nil);
      end;
    end;
    begin
      Registry := TList<TBase>.Create();
      try Plain(); except on E: Exception do WriteLn('plain ', E.Message, ' ', Freed); end;
      Freed := 0;
      try Virt(TBase); except on E: Exception do WriteLn('virt ', E.Message, ' ', Freed); end;
      Freed := 0;
      try ByValue(TBase); except on E: Exception do WriteLn('byvalue ', E.Message, ' ', Freed); end;
      Freed := 0;
      try Nested(); except on E: Exception do WriteLn('nested ', E.Message, ' ', Freed); end;
      Freed := 0;
      Caught();
      WriteLn('caught freed ', Freed);
      Freed := 0;
      try Virt(TDerived); except on E: Exception do WriteLn('registered ', E.Message, ' ', Freed, ' ', Registry.Count); end;
      Registry.Clear();
      WriteLn('cleared ', Freed);
      Registry.Free();
    end.
    ''', 'plain base 11' + #10 + 'virt base 11' + #10 + 'byvalue base 11' + #10 + 'nested holder 101' + #10 +
      'caught base True' + #10 + 'caught freed 11' + #10 +
      'registered base 0 1' + #10 + 'cleared 11');
end;

procedure TUnwindE2ETests.TestDebug_RecordCallArgs_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwRecArgs;
    uses SysUtils;
    type
      TRec = record
        S: string;
        N: Int;
        T: string;
      end;
      TSmall = record
        S: string;
      end;
      TSink = class
        procedure Take(const A: TRec; const B: TRec; N: Int);
      end;
    function MkRec(N: Int): TRec;
    begin
      Result.S := IntToStr(N) + 's';
      Result.T := IntToStr(N) + 't';
      Result.N := N;
    end;
    function MkSmall(N: Int): TSmall;
    begin
      Result.S := IntToStr(N) + 'm';
    end;
    function Boom(): Int;
    begin
      raise Exception.Create('b');
    end;
    procedure TakeRec(const R: TRec; N: Int);
    begin
      WriteLn(R.S, N);
    end;
    procedure TakeRecV(R: TRec; N: Int);
    begin
      WriteLn(R.S, N);
    end;
    procedure TakeSmall(const R: TSmall; N: Int);
    begin
      WriteLn(R.S, N);
    end;
    procedure RaiseIn(const R: TRec);
    begin
      raise Exception.Create('in');
    end;
    procedure TSink.Take(const A: TRec; const B: TRec; N: Int);
    begin
      WriteLn(A.S, B.S, N);
    end;
    procedure A; begin TakeRec(MkRec(1), Boom()); end;
    procedure B; begin TakeRecV(MkRec(2), Boom()); end;
    procedure C; begin TakeSmall(MkSmall(3), Boom()); end;
    procedure D; begin RaiseIn(MkRec(4)); end;
    procedure E;
    var K: TSink;
    begin
      K := TSink.Create();
      K.Take(MkRec(5), MkRec(6), Boom());
    end;
    procedure F; begin TakeRec(MkRec(7), 7); end;
    begin
      try A(); except on X: Exception do WriteLn('a ', X.Message); end;
      try B(); except on X: Exception do WriteLn('b ', X.Message); end;
      try C(); except on X: Exception do WriteLn('c ', X.Message); end;
      try D(); except on X: Exception do WriteLn('d ', X.Message); end;
      try E(); except on X: Exception do WriteLn('e ', X.Message); end;
      F();
    end.
    ''', 'a b' + #10 + 'b b' + #10 + 'c b' + #10 + 'd in' + #10 + 'e b' + #10 + '7s7');
end;

procedure TUnwindE2ETests.TestDebug_OwnedReceivers_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwRecv;
    uses SysUtils;
    type
      TPair = record
        S: string;
        T: string;
      end;
      IThing = interface
        function Echo(N: Int): Int;
        procedure Put(const T: IThing; N: Int);
        function Again(N: Int): IThing;
        function Pair(N: Int): TPair;
      end;
      TThing = class(IThing)
        FN: string;
        constructor Create(const N: string);
        function Echo(N: Int): Int;
        procedure Put(const T: IThing; N: Int);
        function Again(N: Int): IThing;
        function Pair(N: Int): TPair;
      end;
      TObj = class
        function Echo(N: Int): Int;
        procedure Put(N: Int);
      end;
      TVal = record
        S: string;
        function Echo(N: Int): Int;
      end;
      TStr = class
        function ToString(): string; override;
      end;
    constructor TThing.Create(const N: string); begin FN := N; end;
    function TThing.Echo(N: Int): Int; begin Result := N; end;
    procedure TThing.Put(const T: IThing; N: Int); begin WriteLn(N); end;
    function TThing.Again(N: Int): IThing; begin Result := Self; end;
    function TThing.Pair(N: Int): TPair; begin Result.S := FN; Result.T := FN; end;
    function TObj.Echo(N: Int): Int; begin Result := N; end;
    procedure TObj.Put(N: Int); begin WriteLn(N); end;
    function TVal.Echo(N: Int): Int; begin Result := N; end;
    function TStr.ToString(): string; begin raise Exception.Create('ts'); end;
    function Mk(const N: string): IThing; begin Result := TThing.Create(N); end;
    function MkO(): TObj; begin Result := TObj.Create(); end;
    function MkV(N: Int): TVal; begin Result.S := IntToStr(N) + 'v'; end;
    function Boom(): Int; begin raise Exception.Create('b'); end;
    procedure A; begin WriteLn(Mk('a').Echo(Boom())); end;
    procedure B; begin Mk('b').Put(Mk('b2'), Boom()); end;
    procedure C; var T: IThing; begin T := Mk('c').Again(Boom()); end;
    procedure D; var P: TPair; begin P := Mk('d').Pair(Boom()); end;
    procedure E; begin WriteLn(MkO().Echo(Boom())); end;
    procedure F; begin MkO().Put(Boom()); end;
    procedure G; begin WriteLn(MkV(7).Echo(Boom())); end;
    procedure H; var S: string; begin S := TStr.Create().ToString(); end;
    begin
      try A(); except on X: Exception do WriteLn('a ', X.Message); end;
      try B(); except on X: Exception do WriteLn('b ', X.Message); end;
      try C(); except on X: Exception do WriteLn('c ', X.Message); end;
      try D(); except on X: Exception do WriteLn('d ', X.Message); end;
      try E(); except on X: Exception do WriteLn('e ', X.Message); end;
      try F(); except on X: Exception do WriteLn('f ', X.Message); end;
      try G(); except on X: Exception do WriteLn('g ', X.Message); end;
      try H(); except on X: Exception do WriteLn('h ', X.Message); end;
      WriteLn(Mk('h').Echo(8), MkO().Echo(9), MkV(1).Echo(10));
    end.
    ''', 'a b' + #10 + 'b b' + #10 + 'c b' + #10 + 'd b' + #10 + 'e b' + #10 +
      'f b' + #10 + 'g b' + #10 + 'h ts' + #10 + '8910');
end;

procedure TUnwindE2ETests.TestDebug_UnitSectionTryExcept;
var
  Output: string;
  RCode: Int;
  Ok: Boolean;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  WriteFile(FScratch + '/unwsect.pas', '''
    unit unwsect;
    interface
    uses SysUtils;
    var Log: string;
    implementation
    type
      IThing = interface function Name(): string; end;
      TThing = class(IThing) function Name(): string; end;
    function TThing.Name(): string; begin Result := 'n'; end;
    function MkS(N: Int): string; begin Result := IntToStr(N) + 's'; end;
    function MkI(): IThing; begin Result := TThing.Create(); end;
    function Boom(): Int; begin raise Exception.Create('b'); end;
    procedure Take(const S: string; N: Int); begin Log := Log + S; end;
    procedure TakeI(const I: IThing; N: Int); begin Log := Log + I.Name(); end;
    initialization
      try Take(MkS(1), Boom()); except on E: Exception do Log := Log + E.Message; end;
      try TakeI(MkI(), Boom()); except Log := Log + 'y'; end;
      try
        Log := Log + MkS(2) + IntToStr(Boom());
      except
        on E: EConvertError do Log := Log + 'wrong';
        on E: Exception do Log := Log + 'z';
      end;
    finalization
      try raise Exception.Create('f'); except on X: Exception do WriteLn('fin ', X.Message); end;
    end.
    ''');
  Ok := CompileAndRunNativeCLI('''
    program UnwSectProg;
    uses unwsect;
    begin
      WriteLn(Log);
    end.
    ''', True, FScratch, Output, RCode);
  AssertTrue('compile+run: ' + Output, Ok);
  AssertEquals('exit code (output: ' + Output + ')', 0, RCode);
  AssertTrue('sections ran, got: ' + Output,
    Pos('byz' + #10 + 'fin f', Output) >= 0);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TUnwindE2ETests.TestDebug_MainDeferredBases_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwMainPend;
    uses SysUtils;
    type
      TObj = class
        S: string;
        N: Int;
      end;
      TRec = record S: string; N: Int; T: string; end;
    function MkObj(): TObj; begin Result := TObj.Create(); Result.N := 3; Result.S := 'q'; end;
    function MkRec(): TRec; begin Result.S := IntToStr(4) + 'r'; Result.T := 'tt' + IntToStr(5); end;
    function Boom(): Int; begin raise Exception.Create('b'); end;
    var X: Int; S: string;
    begin
      try X := MkObj().N + Boom(); except on E: Exception do WriteLn('a ', E.Message); end;
      try S := MkObj().S + IntToStr(Boom()); except on E: Exception do WriteLn('b ', E.Message); end;
      try X := MkRec().N + Boom(); except on E: Exception do WriteLn('c ', E.Message); end;
      try S := MkRec().S + IntToStr(Boom()); except on E: Exception do WriteLn('d ', E.Message); end;
      X := MkObj().N + MkRec().N;
      WriteLn(X);
    end.
    ''', 'a b' + #10 + 'b b' + #10 + 'c b' + #10 + 'd b' + #10 + '3');
end;

procedure TUnwindE2ETests.TestDebug_RaisingDestructor_DuringUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwDtorRaise;
    uses SysUtils;
    type
      TBad = class
        Tag: string;
        destructor Destroy; override;
      end;
      TCatcher = class
        destructor Destroy; override;
      end;
      TRec = record
        A: TBad;
        S: string;
        B: TBad;
      end;
    var Destroyed: Int;
    destructor TBad.Destroy;
    begin
      Destroyed := Destroyed + 1;
      if Tag = 'raise' then raise Exception.Create('from destructor');
      inherited Destroy();
    end;
    destructor TCatcher.Destroy;
    begin
      Destroyed := Destroyed + 1;
      try raise Exception.Create('inner'); except on E: Exception do WriteLn('dtor ', E.Message); end;
      inherited Destroy();
    end;
    function Boom(): Int; begin raise Exception.Create('first'); end;
    procedure InRecord;
    var R: TRec;
    begin
      R.A := TBad.Create(); R.A.Tag := 'raise';
      R.S := IntToStr(5) + 's';
      R.B := TBad.Create(); R.B.Tag := 'ok';
      Boom();
    end;
    procedure InLocals;
    var A, B: TBad; S: string;
    begin
      A := TBad.Create(); A.Tag := 'raise';
      S := IntToStr(6) + 's';
      B := TBad.Create(); B.Tag := 'ok';
      Boom();
    end;
    procedure Caught;
    var C: TCatcher;
    begin
      C := TCatcher.Create();
      Boom();
    end;
    begin
      try InRecord(); except on E: Exception do WriteLn('rec ', E.Message, ' ', Destroyed); end;
      Destroyed := 0;
      try InLocals(); except on E: Exception do WriteLn('loc ', E.Message, ' ', Destroyed); end;
      Destroyed := 0;
      try Caught(); except on E: Exception do WriteLn('own ', E.Message, ' ', Destroyed); end;
    end.
    ''', 'rec from destructor 2' + #10 + 'loc from destructor 2' + #10 +
      'dtor inner' + #10 + 'own first 1');
end;

procedure TUnwindE2ETests.TestDebug_MainTemporaries_ReleasedOnUnwind;
begin
  AssertLeakFreeOnAll(
    '''
    program UnwMain;
    uses SysUtils;
    type
      IThing = interface
        procedure Hi;
      end;
      TThing = class(IThing)
        procedure Hi;
        destructor Destroy; override;
      end;
      TArr = array of string;
    var
      Freed: Int;
    procedure TThing.Hi;
    begin
    end;
    destructor TThing.Destroy;
    begin
      Freed := Freed + 1;
      inherited Destroy();
    end;
    function MkIntf(): IThing;
    begin
      Result := TThing.Create();
    end;
    function MkArr(): TArr;
    begin
      SetLength(Result, 2);
      Result[0] := 'e' + IntToStr(1);
    end;
    function MkStr(N: Int): string;
    begin
      Result := IntToStr(N) + 'x';
    end;
    procedure Take(I: IThing; const D: TArr; const S: string);
    begin
      raise Exception.Create(S);
    end;
    function BoomS(): string;
    begin
      raise Exception.Create('s');
    end;
    var
      G: string;
    begin
      try Take(MkIntf(), MkArr(), MkStr(7)); except on E: Exception do WriteLn('args ', E.Message, ' ', Freed); end;
      try G := MkStr(8) + BoomS(); except on E: Exception do WriteLn('opnd ', E.Message); end;
    end.
    ''', 'args 7x 1' + #10 + 'opnd s');
end;

initialization
  RegisterTest(TUnwindAsmTests);
  RegisterTest(TUnwindE2ETests);
end.
