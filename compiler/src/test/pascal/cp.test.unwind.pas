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

initialization
  RegisterTest(TUnwindAsmTests);
  RegisterTest(TUnwindE2ETests);
end.
