{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tlist;

{ E2E tests for TList<T> from generics.collections.
  Distinct from cp.test.e2e.tstack which inlines its own class declaration —
  these tests exercise the *generic instantiation* path end-to-end. They are
  the only e2e coverage of stdlib generic classes, and catch link-time bugs
  in vtable/typeinfo emission for generic instances. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ETListTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TListString_AddGetCount;
    procedure TestRun_TListInteger_AddGetCount;
    procedure TestRun_TListInteger_IndexOf;
    procedure TestRun_TListString_IndexOf_NotFound;
    { A generic instantiated over a program-local RECORD type argument must be
      accepted by the in-process analysis flow the test harness uses, exactly as
      the CLI driver accepts it (BUG-041 guard). }
    procedure TestRun_TList_RecordArg_FrontEndAccepts;

    { Class elements are RETAINED on store: an object whose only other
      reference was a local in an exited routine must survive in the list
      (decision recorded in language-rationale: collection ownership). }
    procedure TestRun_TList_ClassElements_RetainedAcrossScope;

    { Default array property: List[i] subscript for read and write. }
    procedure TestRun_TList_DefaultProperty_ReadWrite;
    procedure TestRun_TList_DefaultProperty_Polymorphic;

    { Clear and Free release managed elements (ARC cascade): a class element's
      destructor must run when the list is cleared or freed. }
    procedure TestRun_TList_FreeAndClear_ReleasesElements;

    { The same managed-element release cascade for the other containers
      (BUG-012): Clear/Destroy must release every live element, and the
      element-removing operations must clear the slot they vacate. }
    procedure TestRun_TStack_ClassElements_ReleasedOnDestroy;
    procedure TestRun_TStack_Pop_ReleasesSlot;
    procedure TestRun_TQueue_ClassElements_ReleasedOnDestroy;
    procedure TestRun_TQueue_Dequeue_ReleasesSlot;
    procedure TestRun_TSet_ClassElements_ReleasedOnClear;
    procedure TestRun_TSet_Exclude_ReleasesSlot;
    procedure TestRun_TDictionary_ClassValues_ReleasedOnDestroy;
    procedure TestRun_TDictionary_Remove_ReleasesSlot;
    procedure TestRun_TOrderedDictionary_ClassValues_ReleasedOnDestroy;

    { TQueue<T>.Grow copies into a fresh buffer; the old slots must be
      released or every surviving element leaks a +1. }
    procedure TestRun_TQueue_Grow_ReleasesOldBuffer;
  end;

implementation

const
  SrcTListString = '''
    program P;
    uses generics.collections;
    var
      L: TList<String>;
    begin
      L := TList<String>.Create();
      L.Add('hello');
      L.Add('world');
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free()
    end.
    ''';

  SrcTListInteger = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(2));
      L.Free()
    end.
    ''';

  SrcTListIndexOfInteger = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.IndexOf(10));
      WriteLn(L.IndexOf(20));
      WriteLn(L.IndexOf(30));
      WriteLn(L.IndexOf(99));
      L.Free()
    end.
    ''';

  SrcTListIndexOfStringNotFound = '''
    program P;
    uses generics.collections;
    var
      L: TList<String>;
    begin
      L := TList<String>.Create();
      L.Add('alpha');
      L.Add('beta');
      WriteLn(L.IndexOf('beta'));
      WriteLn(L.IndexOf('gamma'));
      L.Free()
    end.
    ''';

  { BUG-041: TList<TInfo> where TInfo is a program-declared record must
    instantiate under the in-process TUnitLoader.LoadAll ->
    AnalyseUnitForExport -> Analyse(Prog) flow, not only via the CLI driver.
    Kept to Create/Count/Free — the record-value Add/Get lifecycle is a
    separate concern (BUG-002). }
  SrcTListRecordArg = '''
    program P;
    uses generics.collections;
    type TInfo = record X: Integer; end;
    var L: TList<TInfo>;
    begin
      L := TList<TInfo>.Create();
      WriteLn(L.Count);
      L.Free()
    end.
    ''';

procedure TE2ETListTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tlist')
end;

procedure TE2ETListTests.TestRun_TListString_AddGetCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Count=2 printed',  Pos('2',     Output) >= 0);
  AssertTrue('Get(0)=hello',     Pos('hello', Output) >= 0);
  AssertTrue('Get(1)=world',     Pos('world', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListInteger_AddGetCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListInteger, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Count=3 printed', Pos('3',  Output) >= 0);
  AssertTrue('Get(0)=10',       Pos('10', Output) >= 0);
  AssertTrue('Get(2)=30',       Pos('30', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListInteger_IndexOf;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListIndexOfInteger, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('IndexOf(10)=0', Pos('0',  Output) >= 0);
  AssertTrue('IndexOf(20)=1', Pos('1',  Output) >= 0);
  AssertTrue('IndexOf(30)=2', Pos('2',  Output) >= 0);
  AssertTrue('IndexOf(99)=-1 (missing)', Pos('-1', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListString_IndexOf_NotFound;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListIndexOfStringNotFound, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('IndexOf(beta)=1',          Pos('1',  Output) >= 0);
  AssertTrue('IndexOf(gamma)=-1',        Pos('-1', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TList_RecordArg_FrontEndAccepts;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListRecordArg, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Count=0 printed', Pos('0', Output) >= 0);
end;

const
  SrcTListClassRetain = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
      end;
    procedure Fill(L: TList<TC>; S: TStack<TC>);
    var C: TC;
    begin
      C := TC.Create();
      C.N := 77;
      L.Add(C);
      C := TC.Create();
      C.N := 88;
      S.Push(C);
    end;
    var
      L: TList<TC>;
      S: TStack<TC>;
    begin
      L := TList<TC>.Create();
      S := TStack<TC>.Create();
      Fill(L, S);
      writeln(L.Get(0).N);
      writeln(S.Peek().N);
    end.
    ''';

procedure TE2ETListTests.TestRun_TList_ClassElements_RetainedAcrossScope;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListClassRetain, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('retained elements readable (qbe)', '77' + #10 + '88' + #10, Output);
  AssertTrue('compile+link+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListClassRetain, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('retained elements readable (native)', '77' + #10 + '88' + #10, Output);
end;

const
  SrcTListDefaultRW = '''
    program P;
    uses Generics.Collections;
    var lst: TList<Integer>;
    begin
      lst := TList<Integer>.Create;
      lst.Add(1); lst.Add(2);
      lst[0] := 100; lst[1] := 200;
      WriteLn(lst[0] + lst[1]);
      lst.Free()
    end.
    ''';

  SrcTListDefaultPoly = '''
    program P;
    uses Generics.Collections;
    type
      TShape = class function Area: Integer; virtual; begin Result := 0 end; end;
      TBox = class(TShape)
        FS: Integer;
        constructor Create(s: Integer); begin FS := s end;
        function Area: Integer; override; begin Result := FS * FS end;
      end;
    var lst: TList<TShape>; i, total: Integer;
    begin
      lst := TList<TShape>.Create;
      lst.Add(TBox.Create(3)); lst.Add(TBox.Create(4));
      total := 0;
      for i := 0 to lst.Count - 1 do total := total + lst[i].Area();
      WriteLn(total);
      lst.Free()
    end.
    ''';

procedure TE2ETListTests.TestRun_TList_DefaultProperty_ReadWrite;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListDefaultRW, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('List[i] read/write (qbe)', '300' + #10, Output);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListDefaultRW, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('List[i] read/write (native)', '300' + #10, Output);
end;

procedure TE2ETListTests.TestRun_TList_DefaultProperty_Polymorphic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListDefaultPoly, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('List[i].Area (qbe)', '25' + #10, Output);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListDefaultPoly, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('List[i].Area (native)', '25' + #10, Output);
end;

const
  SrcTListFreeClear = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      L: TList<TC>;
    begin
      L := TList<TC>.Create();
      L.Add(TC.Create(1));
      L.Add(TC.Create(2));
      L.Clear();
      WriteLn('cleared');
      L.Add(TC.Create(3));
      L.Free();
      WriteLn('done')
    end.
    ''';

procedure TE2ETListTests.TestRun_TList_FreeAndClear_ReleasesElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Clear releases elements 1 and 2; the final Free releases element 3 — each
    destructor fires, proving the managed-element release cascade. }
  AssertRTLRunsOnAll(SrcTListFreeClear,
    'd1' + #10 + 'd2' + #10 + 'cleared' + #10 + 'd3' + #10 + 'done' + #10, 0);
end;

{ ------------------------------------------------------------------ }
{ BUG-012 — the other containers must release managed elements too.    }
{ Each program declares a class whose destructor prints, so the exact  }
{ release points are visible in stdout ordering.                       }
{ ------------------------------------------------------------------ }

const
  SrcTStackDestroy = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      S: TStack<TC>;
    begin
      S := TStack<TC>.Create();
      S.Push(TC.Create(1));
      S.Push(TC.Create(2));
      S.Clear();
      WriteLn('cleared');
      S.Push(TC.Create(3));
      S.Free();
      WriteLn('done')
    end.
    ''';

  { Pop hands ownership to the caller; the vacated slot must not keep a
    second reference alive.  Freeing the popped object here must run its
    destructor exactly once, before the stack is freed. }
  SrcTStackPop = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      S: TStack<TC>;
      C: TC;
    begin
      S := TStack<TC>.Create();
      S.Push(TC.Create(1));
      C := S.Pop();
      WriteLn('popped', C.N);
      C := nil;
      WriteLn('nilled');
      S.Free();
      WriteLn('done')
    end.
    ''';

  SrcTQueueDestroy = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      Q: TQueue<TC>;
    begin
      Q := TQueue<TC>.Create();
      Q.Enqueue(TC.Create(1));
      Q.Enqueue(TC.Create(2));
      Q.Clear();
      WriteLn('cleared');
      Q.Enqueue(TC.Create(3));
      Q.Free();
      WriteLn('done')
    end.
    ''';

  { Enqueue/Dequeue past the initial capacity so FHead wraps — the release
    walk must follow the circular layout, not slots 0..FCount-1. }
  SrcTQueueDequeue = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      Q: TQueue<TC>;
      C: TC;
      I: Integer;
    begin
      Q := TQueue<TC>.Create();
      for I := 1 to 3 do
        Q.Enqueue(TC.Create(I));
      for I := 1 to 3 do
      begin
        C := Q.Dequeue();
        WriteLn('got', C.N);
        C := nil
      end;
      WriteLn('drained');
      Q.Enqueue(TC.Create(9));
      Q.Free();
      WriteLn('done')
    end.
    ''';

  SrcTSetClear = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      S: TSet<TC>;
    begin
      S := TSet<TC>.Create();
      S.Include(TC.Create(1));
      S.Include(TC.Create(2));
      S.Clear();
      WriteLn('cleared');
      S.Include(TC.Create(3));
      S.Free();
      WriteLn('done')
    end.
    ''';

  { Exclude shifts the tail down; the vacated slot must be cleared or the
    excluded element stays alive through a duplicated reference. }
  SrcTSetExclude = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      S: TSet<TC>;
      A: TC;
      B: TC;
    begin
      S := TSet<TC>.Create();
      A := TC.Create(1);
      B := TC.Create(2);
      S.Include(A);
      S.Include(B);
      S.Exclude(A);
      A := nil;
      WriteLn('excluded');
      B := nil;
      S.Free();
      WriteLn('done')
    end.
    ''';

  SrcTDictDestroy = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      D: TDictionary<String, TC>;
    begin
      D := TDictionary<String, TC>.Create();
      D.Add('a', TC.Create(1));
      D.Add('b', TC.Create(2));
      D.Clear();
      WriteLn('cleared');
      D.Add('c', TC.Create(3));
      D.Free();
      WriteLn('done')
    end.
    ''';

  SrcTDictRemove = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      D: TDictionary<String, TC>;
    begin
      D := TDictionary<String, TC>.Create();
      D.Add('a', TC.Create(1));
      D.Add('b', TC.Create(2));
      D.Remove('a');
      WriteLn('removed');
      D.Free();
      WriteLn('done')
    end.
    ''';

  SrcTOrdDictDestroy = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      D: TOrderedDictionary<String, TC>;
    begin
      D := TOrderedDictionary<String, TC>.Create();
      D.Add('a', TC.Create(1));
      D.Add('b', TC.Create(2));
      D.Remove('a');
      WriteLn('removed');
      D.Free();
      WriteLn('done')
    end.
    ''';

procedure TE2ETListTests.TestRun_TStack_ClassElements_ReleasedOnDestroy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTStackDestroy,
    'd1' + #10 + 'd2' + #10 + 'cleared' + #10 + 'd3' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TStack_Pop_ReleasesSlot;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTStackPop,
    'popped1' + #10 + 'd1' + #10 + 'nilled' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TQueue_ClassElements_ReleasedOnDestroy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTQueueDestroy,
    'd1' + #10 + 'd2' + #10 + 'cleared' + #10 + 'd3' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TQueue_Dequeue_ReleasesSlot;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTQueueDequeue,
    'got1' + #10 + 'd1' + #10 + 'got2' + #10 + 'd2' + #10 +
    'got3' + #10 + 'd3' + #10 + 'drained' + #10 + 'd9' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TSet_ClassElements_ReleasedOnClear;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTSetClear,
    'd1' + #10 + 'd2' + #10 + 'cleared' + #10 + 'd3' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TSet_Exclude_ReleasesSlot;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTSetExclude,
    'd1' + #10 + 'excluded' + #10 + 'd2' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TDictionary_ClassValues_ReleasedOnDestroy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTDictDestroy,
    'd1' + #10 + 'd2' + #10 + 'cleared' + #10 + 'd3' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TDictionary_Remove_ReleasesSlot;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTDictRemove,
    'd1' + #10 + 'removed' + #10 + 'd2' + #10 + 'done' + #10, 0);
end;

procedure TE2ETListTests.TestRun_TOrderedDictionary_ClassValues_ReleasedOnDestroy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTOrdDictDestroy,
    'd1' + #10 + 'removed' + #10 + 'd2' + #10 + 'done' + #10, 0);
end;

const
  { Six elements against an initial capacity of 4 forces two Grow rounds. }
  SrcTQueueGrow = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
      end;
    constructor TC.Create(AN: Integer);
    begin N := AN end;
    destructor TC.Destroy;
    begin WriteLn('d', N) end;
    var
      Q: TQueue<TC>;
      I: Integer;
    begin
      Q := TQueue<TC>.Create();
      for I := 1 to 6 do
        Q.Enqueue(TC.Create(I));
      WriteLn('filled');
      Q.Free();
      WriteLn('done')
    end.
    ''';

procedure TE2ETListTests.TestRun_TQueue_Grow_ReleasesOldBuffer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcTQueueGrow,
    'filled' + #10 + 'd1' + #10 + 'd2' + #10 + 'd3' + #10 +
    'd4' + #10 + 'd5' + #10 + 'd6' + #10 + 'done' + #10, 0);
end;

initialization
  RegisterTest(TE2ETListTests);

end.
