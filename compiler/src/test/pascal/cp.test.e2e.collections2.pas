{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.collections2;

{ E2E tests for TObjectList and TStringList collection classes. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ECollections2Tests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TObjectList_AddGetCount;
    procedure TestRun_TObjectList_Delete;
    procedure TestRun_Collections_Valgrind;
    procedure TestRun_TwoDictInstancesInUnit_BothLink;
    { BUG-20260724 pass-borrowed-string-by-value over-release: a routine
      receives a string as a BORROWED const param and passes it by value into
      TDictionary lookups (ContainsKey / TryGetValue).  The lookup key params
      are now const (pure borrow — no callee retain/release pair), so the
      borrowed transient key survives the calls and is not double-freed.
      Runs clean under valgrind. }
    procedure TestRun_DictLookup_BorrowedConstKey_NoDoubleFree;
    procedure TestRun_IntfFreeFunc_GenericReturn_Compiles;
    procedure TestRun_DefaultProp_StringList_And_ObjectList;

    { Pointer-write ARC for interface and dyn-array pointees (BUG-012 part 2).
      `P^ := V` is the primitive every generic container uses for its element
      slots.  It retained strings and class refs but silently dropped
      interfaces and dyn-arrays, so the element died with its source variable
      and the slot dangled — a use-after-free, not merely a leak. }
    procedure TestRun_PointerWrite_Interface_RetainsAndReleases;
    procedure TestRun_PointerWrite_DynArray_RetainsAndReleases;

    { Pointer-READ ARC for interfaces (BUG-012 part 3).  The read counterpart
      of the write tests above: `G := P^` and `P^.Method()` through a ^IFoo.
      The native backend could not address an interface through a pointer at
      all — its interface handling is named-slot based — so the read was a
      hard codegen error and `@Slot`-style out-parameter fills segfaulted. }
    procedure TestRun_PointerRead_Interface_RetainsAndReleases;
    procedure TestRun_PointerFill_Interface_OutlivesCallee;

    { TList<IFoo> end-to-end.  Monomorphising TList<T> at an interface makes
      `Result := Src^` in TList<T>.Get an sret-Result read through a ^IFoo,
      which was unsupported — the container could not be instantiated at all.
      The list must OWN its elements: they stay alive while stored and are
      released on Free. }
    procedure TestRun_TListOfInterface_RetainsElementsUntilFree;

    { Chained dispatch on an interface-returning METHOD result
      (`B.Get().Val()`).  EmitInterfaceCall routed a TFuncCallExpr receiver
      through the sret convention but not a TMethodCallExpr one, so the
      method-call form fell through to the named-slot path with an EMPTY
      name and emitted `movq _obj(%rip)` / `movq _itab(%rip)` — symbols that
      are never defined.  The linker bound them to arbitrary addresses, so
      native compiled clean and segfaulted at run time while QBE was correct. }
    procedure TestRun_ChainedIntfMethodCall_Dispatches;

    { Deref-dispatch `P^.Method()` is NOT covered here: the parser shapes
      `P^.Name` as a TFieldAccessExpr unconditionally and never checks for a
      following '(', so the form is rejected at PARSE time for classes and
      records too — it is a general postfix-parse gap, not an interface or
      codegen one.  Copying the fat pointer into a local first
      (`G := P^; G.Method()`) is covered by the read test above. }
  end;

implementation

procedure TE2ECollections2Tests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-collections2');
end;

const
  // Note: uses //-style comment here because the text contains curly braces.
  SrcTObjectListAddGetCount = '''
    program P;
    type
      TObjectList = class
        FData:     ^Pointer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var OldCap, NewCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4
          else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
          Self.FCapacity := NewCap
        end;
        function Add(AObject: Pointer): Integer;
        var Dest: ^Pointer;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
          Dest^       := AObject;
          Self.FCount := Self.FCount + 1;
          Result      := Self.FCount - 1
        end;
        function Get(AIndex: Integer): Pointer;
        var Src: ^Pointer;
        begin
          Src    := Self.FData + AIndex * SizeOf(Pointer);
          Result := Src^
        end;
        procedure Delete(AIndex: Integer);
        var I: Integer; Dst, Src: ^Pointer;
        begin
          I := AIndex;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(Pointer);
            Src  := Self.FData + (I + 1) * SizeOf(Pointer);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        property Count: Integer read FCount;
      end;
    var
      L:  TObjectList;
      P1, P2: Pointer;
    begin
      L  := TObjectList.Create();
      P1 := GetMem(1);
      P2 := GetMem(1);
      L.Add(P1);
      L.Add(P2);
      L.Add(nil);
      WriteLn(L.Count);
      WriteLn(L.Get(0) = P1);
      WriteLn(L.Get(1) = P2)
    end.
    ''';

  SrcTObjectListDelete = '''
    program P;
    type
      TObjectList = class
        FData:     ^Pointer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var OldCap, NewCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4
          else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
          Self.FCapacity := NewCap
        end;
        function Add(AObject: Pointer): Integer;
        var Dest: ^Pointer;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
          Dest^       := AObject;
          Self.FCount := Self.FCount + 1;
          Result      := Self.FCount - 1
        end;
        procedure Delete(AIndex: Integer);
        var I: Integer; Dst, Src: ^Pointer;
        begin
          I := AIndex;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(Pointer);
            Src  := Self.FData + (I + 1) * SizeOf(Pointer);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        property Count: Integer read FCount;
      end;
    var L: TObjectList;
    begin
      L := TObjectList.Create();
      L.Add(GetMem(1));
      L.Add(GetMem(1));
      L.Add(GetMem(1));
      L.Delete(1);
      WriteLn(L.Count)
    end.
    ''';

  SrcCollectionsValgrind =
    '''
        program P;
        type
          TObjectList = class
            FData: ^Pointer; FCount: Integer; FCapacity: Integer;
            procedure Grow;
            var OldCap, NewCap: Integer;
            begin
              OldCap := Self.FCapacity;
              if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
              Self.FData := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
              Self.FCapacity := NewCap
            end;
            function Add(AObject: Pointer): Integer;
            var Dest: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              Dest := Self.FData + Self.FCount * SizeOf(Pointer);
              Dest^ := AObject;
              Self.FCount := Self.FCount + 1;
              Result := Self.FCount - 1
            end;
            procedure Destroy;
            begin
              FreeMem(Self.FData);
              Self.FData := nil; Self.FCount := 0; Self.FCapacity := 0
            end;
            property Count: Integer read FCount;
          end;
          TStringList = class
            FStrings: ^string; FObjects: ^Pointer;
            FCount: Integer; FCapacity: Integer;
            procedure Grow;
            var OldCap, NewCap: Integer;
            begin
              OldCap := Self.FCapacity;
              if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
              Self.FStrings := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
              Self.FObjects := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
              ZeroMem(Self.FStrings + OldCap * SizeOf(string),
                      (NewCap - OldCap) * SizeOf(string));
              Self.FCapacity := NewCap
            end;
            procedure Destroy;
            var I: Integer; Ptr: ^string;
            begin
              I := 0;
              while I < Self.FCount do
              begin
                Ptr := Self.FStrings + I * SizeOf(string); Ptr^ := nil; I := I + 1
              end;
              FreeMem(Self.FStrings); FreeMem(Self.FObjects);
              Self.FStrings := nil; Self.FObjects := nil;
              Self.FCount := 0; Self.FCapacity := 0
            end;
            function Add(S: string): Integer;
            var StrP: ^string; ObjP: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              StrP := Self.FStrings + Self.FCount * SizeOf(string);
              ObjP := Self.FObjects + Self.FCount * SizeOf(Pointer);
              StrP^ := S; ObjP^ := nil;
              Result := Self.FCount; Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): string;
            var Ptr: ^string;
            begin
              Ptr := Self.FStrings + AIndex * SizeOf(string); Result := Ptr^
            end;
            property Count: Integer read FCount;
          end;
        var OL: TObjectList; SL: TStringList;
        begin
          OL := TObjectList.Create();
          OL.Add(nil); OL.Add(nil);
          SL := TStringList.Create();
          SL.Add('hello'); SL.Add('world');
          WriteLn(OL.Count);
          WriteLn(SL.Get(0))
        end.
        ''';

procedure TE2ECollections2Tests.TestRun_TObjectList_AddGetCount;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListAddGetCount, Output, RCode));
  AssertEquals('count=3', '3', Trim(Copy(Output, 0, Pos(#10, Output))));
end;

procedure TE2ECollections2Tests.TestRun_TObjectList_Delete;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListDelete, Output, RCode));
  AssertEquals('count after delete=2', '2', Trim(Output));
end;

procedure TE2ECollections2Tests.TestRun_Collections_Valgrind;
var OK: Boolean; Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { real ARC-leak guard (valgrind is blind to the mmap allocator) }
  AssertLeakFreeOnAll(SrcCollectionsValgrind, '');
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcCollectionsValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('Collections Valgrind check failed:' + #10 + Log);
  end;
end;

{ Regression: a unit that holds two distinct instantiations of the same
  generic whose template inherits from a generic interface (TDictionary<K,V>
  derives from IMap<K,V>).  The first instantiation used to free the generic-
  template AST node it shares; the second lookup then saw a wrong-class object
  and silently mis-wired the instance — no TObject parent, no vtable — so the
  second instance's $vtable_... symbol was referenced but never emitted and the
  link failed.  Retaining templates in the symbol table fixes it.  Both
  instances must now compile, link and run. }
procedure TE2ECollections2Tests.TestRun_TwoDictInstancesInUnit_BothLink;
const
  UnitSrc = '''
    unit twodicts;
    interface
    uses Generics.Collections;
    type
      THolder = class
      public
        Ints:  TDictionary<string, Integer>;
        Bools: TDictionary<string, Boolean>;
        procedure Fill;
        function Total: Integer;
      end;
    implementation
    procedure THolder.Fill;
    begin
      Self.Ints  := TDictionary<string, Integer>.Create();
      Self.Bools := TDictionary<string, Boolean>.Create();
      Self.Ints.Add('a', 10);
      Self.Ints.Add('b', 20);
      Self.Bools.Add('x', True)
    end;
    function THolder.Total: Integer;
    begin
      Result := Self.Ints.Count + Self.Bools.Count
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses twodicts;
    var h: THolder;
    begin
      h := THolder.Create();
      h.Fill();
      WriteLn(h.Total());
      h.Free()
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('twodicts', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Ints(2) + Bools(1) = 3', '3' + #10, Output);
end;

{ Regression (BUG-20260724 pass-borrowed-string-by-value over-release):
  Look receives Key as a BORROWED const string param, then passes it BY VALUE
  into TDictionary.ContainsKey / TryGetValue.  The key is an owned concat
  transient the caller still owns; before the fix, arm64 passed the borrowed
  Key without a caller-side pin AND the lookup key params were by-value (a
  callee retain/release pair), so the transient was released one too many and
  double-freed on scope exit — the FFrame.TryGetValue(const AName) cascade
  found on macOS arm64.  Making the lookup key params const removes the callee
  pair entirely (a lookup never owns its key), and the arm64 caller now pins a
  borrowed aliasable source anyway.  Must run clean and leak-free on BOTH
  backends. }
const
  DictKeyUnitSrc = '''
    unit dictkey;
    interface
    uses Generics.Collections;
    type
      THolder = class
      public
        D: TDictionary<string, Integer>;
        procedure Init;
        // Look receives Key as a BORROWED const param and passes it BY VALUE
        // into the dictionary lookups — the exact FFrame.TryGetValue(const
        // AName) shape that over-released on arm64.
        function Look(const Key: string): Integer;
      end;
    implementation
    procedure THolder.Init;
    begin
      Self.D := TDictionary<string, Integer>.Create()
    end;
    function THolder.Look(const Key: string): Integer;
    var V: Integer;
    begin
      Result := -1;
      if Self.D.ContainsKey(Key) then
        if Self.D.TryGetValue(Key, V) then
          Result := V
    end;
    end.
    ''';
  DictKeyDrvSrc = '''
    program P;
    uses dictkey;
    var
      H: THolder;
      S: string;
    begin
      H := THolder.Create();
      H.Init();
      S := 'alpha' + 'beta';   // owned concat transient key
      H.D.Add(S, 42);
      WriteLn(H.Look(S));
      WriteLn(S);               // the borrowed key must still be intact
      H.D.Destroy();
      H.Free()
    end.
    ''';

procedure TE2ECollections2Tests.TestRun_DictLookup_BorrowedConstKey_NoDoubleFree;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('dictkey', DictKeyUnitSrc, DictKeyDrvSrc,
      Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('lookup value + intact key', '42' + #10 + 'alphabeta' + #10,
    Output);
end;

{ Regression: a unit's INTERFACE-section free function (not a class method)
  whose return type is a generic instantiation such as TList<string> used to
  fail semantic analysis with "Unknown return type 'TList<string>'".  The
  interface free-function path resolved the return type through a plain
  FindType lookup, which never attempts generic instantiation, whereas the
  class-method path goes through FindTypeOrInstantiate.  Switching the
  free-function path to FindTypeOrInstantiate fixes it.  The same generic
  return type as a class method, and as an impl-section free function, already
  worked — those must keep working. }
procedure TE2ECollections2Tests.TestRun_IntfFreeFunc_GenericReturn_Compiles;
const
  UnitSrc = '''
    unit freefunc;
    interface
    uses Generics.Collections;
    function MakeList: TList<string>;
    implementation
    function MakeList: TList<string>;
    begin
      Result := TList<string>.Create();
      Result.Add('a');
      Result.Add('b')
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses Generics.Collections, freefunc;
    var L: TList<string>;
    begin
      L := MakeList();
      WriteLn(L.Count);
      L.Free()
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('freefunc', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('list count', '2' + #10, Output);
end;

{ Regression (GitHub #138): the real classes.TStringList and contnrs.TObjectList
  must both carry a `default` indexed property so SL[i] / OL[i] work as sugar
  for SL.Strings[i] / OL.Items[i].  TStringList already had it; TObjectList did
  not.  The chained form TStringList(OL[0])[1] — a typecast whose operand is
  itself a default-property subscript, indexed again by a default property —
  crashed the compiler (unbounded re-analysis of the rewritten subscript node);
  AnalyseStringSubscriptExpr now guards against re-analysis via ResolvedType. }
procedure TE2ECollections2Tests.TestRun_DefaultProp_StringList_And_ObjectList;
const
  Src = '''
    program P;
    uses classes, contnrs;
    var SL: TStringList; OL: TObjectList; i: Integer;
    begin
      SL := TStringList.Create;
      SL.Add('alpha');
      SL.Add('beta');
      for i := 0 to SL.Count - 1 do
        WriteLn(SL[i]);            // default property read
      SL[0] := 'ALPHA';           // default property write
      WriteLn(SL[0]);
      OL := TObjectList.Create(False);
      OL.Add(SL);
      WriteLn(TStringList(OL[0])[1]);   // chained: cast(OL default) then default
      SL.Free();
      OL.Free()
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { CompileAndRunWithRTL runs on BOTH backends and asserts parity, and puts the
    RTL + stdlib (classes, contnrs) on the unit search path. }
  AssertTrue('compile+run', CompileAndRunWithRTL(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('default-property output',
    'alpha' + #10 + 'beta' + #10 + 'ALPHA' + #10 + 'beta' + #10, Output);
end;

const
  { The interface is stored into the slot inside Fill and its only other
    reference (the local A) dies at Fill's exit.  If the pointer write does
    not retain, the destructor fires BEFORE 'filled' and the slot dangles. }
  SrcPointerWriteIntf = '''
    program P;
    type
      IFoo = interface
        function Value: Integer;
      end;
      TFoo = class(IFoo)
        FN: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
        function Value: Integer;
      end;
    constructor TFoo.Create(AN: Integer);
    begin FN := AN end;
    destructor TFoo.Destroy;
    begin WriteLn('d', FN) end;
    function TFoo.Value: Integer;
    begin Result := FN end;
    var
      Slot: ^IFoo;
    procedure Fill;
    var
      A: IFoo;
    begin
      A := TFoo.Create(41);
      Slot^ := A
    end;
    begin
      Slot := GetMem(16);
      ZeroMem(Slot, 16);
      Fill();
      WriteLn('filled');
      Slot^ := nil;
      WriteLn('cleared');
      FreeMem(Slot);
      WriteLn('done')
    end.
    ''';

  { Same shape for a dynamic array: the buffer must outlive the local that
    built it, and still hold its contents when read back. }
  SrcPointerWriteDynArray = '''
    program P;
    type
      TArr = array of Integer;
    var
      Slot: ^TArr;
    procedure Fill;
    var
      A: TArr;
    begin
      SetLength(A, 3);
      A[0] := 77;
      Slot^ := A
    end;
    var
      B: TArr;
    begin
      Slot := GetMem(8);
      ZeroMem(Slot, 8);
      Fill();
      B := Slot^;
      WriteLn(B[0]);
      WriteLn(Length(B));
      SetLength(B, 0);
      FreeMem(Slot);
      WriteLn('done')
    end.
    ''';

procedure TE2ECollections2Tests.TestRun_PointerWrite_Interface_RetainsAndReleases;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcPointerWriteIntf,
    'filled' + #10 + 'd41' + #10 + 'cleared' + #10 + 'done' + #10, 0);
end;

procedure TE2ECollections2Tests.TestRun_PointerWrite_DynArray_RetainsAndReleases;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcPointerWriteDynArray,
    '77' + #10 + '3' + #10 + 'done' + #10, 0);
end;

const
  { `G := P^` — reading an interface back out of a pointer slot.  G must own
    its own reference: clearing the original slot first must NOT destroy the
    object, and the destructor must fire only when G itself is cleared. }
  SrcPointerReadIntf = '''
    program P;
    type
      IFoo = interface
        function Value: Integer;
      end;
      TFoo = class(IFoo)
        FN: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
        function Value: Integer;
      end;
    constructor TFoo.Create(AN: Integer);
    begin FN := AN end;
    destructor TFoo.Destroy;
    begin WriteLn('d', FN) end;
    function TFoo.Value: Integer;
    begin Result := FN end;
    var
      Slot: ^IFoo;
      G: IFoo;
    begin
      Slot := GetMem(16);
      ZeroMem(Slot, 16);
      Slot^ := TFoo.Create(41);
      G := Slot^;
      WriteLn(G.Value());
      Slot^ := nil;
      WriteLn('slot cleared');
      G := nil;
      WriteLn('g cleared');
      FreeMem(Slot);
      WriteLn('done')
    end.
    ''';

  { The out-parameter fill shape: Fill stores into the caller's interface
    variable through a ^IFoo and its own local reference then dies.  If the
    pointer write does not retain, or the caller's slot is not treated as an
    owning interface, the object is destroyed at Fill's exit and the caller
    holds a dangling fat pointer — a use-after-free, which is what made this
    program segfault on the native backend. }
  SrcPointerFillIntf = '''
    program P;
    type
      IFoo = interface
        procedure Ping;
      end;
      TFoo = class(IFoo)
        procedure Ping;
        destructor Destroy; override;
      end;
    procedure TFoo.Ping;
    begin WriteLn('ping') end;
    destructor TFoo.Destroy;
    begin WriteLn('destroyed') end;
    procedure Fill(P: ^IFoo);
    var
      F: IFoo;
    begin
      F := TFoo.Create();
      P^ := F;
      WriteLn('filled')
    end;
    var
      Slot: IFoo;
    begin
      WriteLn('start');
      Fill(@Slot);
      WriteLn('after fill');
      Slot := nil;
      WriteLn('done')
    end.
    ''';

procedure TE2ECollections2Tests.TestRun_PointerRead_Interface_RetainsAndReleases;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(SrcPointerReadIntf,
    '41' + #10 + 'slot cleared' + #10 + 'd41' + #10 + 'g cleared' + #10 +
    'done' + #10, 0);
end;

procedure TE2ECollections2Tests.TestRun_PointerFill_Interface_OutlivesCallee;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 'destroyed' MUST come after 'after fill' — if it appears earlier the
    callee's local took the object with it and the caller's slot dangles. }
  AssertRTLRunsOnAll(SrcPointerFillIntf,
    'start' + #10 + 'filled' + #10 + 'after fill' + #10 + 'destroyed' + #10 +
    'done' + #10, 0);
end;

const
  { TList<IFoo>: the container fills its element slots with `Dest^ := Value`
    and reads them back with `Result := Src^` (an sret-Result read through a
    ^IFoo).  G takes its own reference, so clearing G must NOT destroy either
    element — both die only when the list is freed, proving the list owns
    them.  `L.Get(0)` is used rather than `L[0]`: the default-property
    subscript on an interface-typed element is still unsupported on both
    backends (it fails loud). }
  SrcTListOfInterface = '''
    program P;
    uses generics.collections;
    type
      IFoo = interface
        function Value: Integer;
      end;
      TFoo = class(IFoo)
        FN: Integer;
        constructor Create(AN: Integer);
        destructor Destroy; override;
        function Value: Integer;
      end;
    constructor TFoo.Create(AN: Integer);
    begin FN := AN end;
    destructor TFoo.Destroy;
    begin WriteLn('d', FN) end;
    function TFoo.Value: Integer;
    begin Result := FN end;
    var
      L: TList<IFoo>;
      G: IFoo;
    begin
      L := TList<IFoo>.Create();
      L.Add(TFoo.Create(1));
      L.Add(TFoo.Create(2));
      WriteLn(L.Count);
      G := L.Get(0);
      WriteLn(G.Value());
      G := nil;
      WriteLn('cleared g');
      L.Free();
      WriteLn('done')
    end.
    ''';

  { Chained dispatch on an interface-returning METHOD result.  Both the
    generic (TBox<IFoo>.Get) and plain (Make) forms are exercised: only the
    generic one crashed, but the plain one pins that the existing
    TFuncCallExpr receiver path keeps working.  The two-step form is printed
    first so a failure distinguishes "dispatch broken" from "chaining
    broken". }
  SrcChainedIntfCall = '''
    program P;
    type
      IFoo = interface
        function Value: Integer;
      end;
      TFoo = class(IFoo)
        FN: Integer;
        constructor Create(AN: Integer);
        function Value: Integer;
      end;
      TBox<T> = class
        FItem: T;
        procedure Put(const A: T);
        function Get: T;
      end;
    constructor TFoo.Create(AN: Integer);
    begin FN := AN end;
    function TFoo.Value: Integer;
    begin Result := FN end;
    procedure TBox<T>.Put(const A: T);
    begin FItem := A end;
    function TBox<T>.Get: T;
    begin Result := FItem end;
    function Make: IFoo;
    begin Result := TFoo.Create(7) end;
    var
      B: TBox<IFoo>;
      G: IFoo;
    begin
      B := TBox<IFoo>.Create();
      B.Put(TFoo.Create(5));
      G := B.Get();
      WriteLn(G.Value());
      WriteLn(B.Get().Value());
      WriteLn(Make().Value());
      B.Free();
      WriteLn('done')
    end.
    ''';

procedure TE2ECollections2Tests.TestRun_ChainedIntfMethodCall_Dispatches;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Before the fix native emitted movq _obj(%rip) for the B.Get() receiver —
    an undefined symbol — and segfaulted here while QBE printed 5. }
  AssertRTLRunsOnAll(SrcChainedIntfCall,
    '5' + #10 + '5' + #10 + '7' + #10 + 'done' + #10, 0);
end;

procedure TE2ECollections2Tests.TestRun_TListOfInterface_RetainsElementsUntilFree;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 'd1'/'d2' MUST come after 'cleared g' — if an element dies earlier the
    list was not retaining it and the slot dangles. }
  AssertRTLRunsOnAll(SrcTListOfInterface,
    '2' + #10 + '1' + #10 + 'cleared g' + #10 + 'd1' + #10 + 'd2' + #10 +
    'done' + #10, 0);
end;

initialization
  RegisterTest(TE2ECollections2Tests);

end.
