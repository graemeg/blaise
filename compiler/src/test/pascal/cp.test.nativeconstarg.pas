{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativeconstarg;

{ Assembly-level tests for shape-aware const-string argument handling in the
  NATIVE x86-64 backend — the port of the QBE backend's convention (see
  cp.test.constarg.pas for the QBE twins and the full classification table).

  Native convention after the port:

    callee    — const params of ANY kind (including string) emit no
                entry-retain/exit-release pair.
    caller    — protects const-string arguments by shape:
                borrowed (literals, named consts, plain safe locals) → no ops;
                consume (owned +1 returns) → one post-call release;
                pin (globals, fields, concat transients, aliasable locals)
                → AddRef before the call, release after. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target, cp.test.targets, uDebugFacts;

type
  TNativeConstArgTests = class(TTestCase)
  private
    function GenAsm(const ASrc: string): string;
    { Extract one emitted function's assembly (from 'Name:' to its
      '.type Name, @function' trailer) so assertions are not polluted by
      other functions' code. }
    function FuncRegion(const AAsm, AName: string): string;
    function CountOccurrences(const ANeedle, AHaystack: string): Integer;
  published
    procedure TestCallee_ConstStringParam_NoEntryExitPair;
    procedure TestCallee_ValueStringParam_KeepsEntryExitPair;
    procedure TestConstArg_ParamForward_NoArcOps;
    procedure TestConstArg_Literal_NoPin;
    procedure TestConstArg_LocalVar_NoPin;
    procedure TestConstArg_GlobalVar_Pins;
    procedure TestConstArg_OwnedReturn_ConsumeOnly;
    procedure TestConstArg_Concat_Pins;
    procedure TestConstArg_VarStringSibling_Pins;
    procedure TestConstArg_AddrTakenLocal_Pins;
    procedure TestConstArg_CapturedLocal_Pins;
    procedure TestConstArg_InterfaceDispatch_ConcatPins;
    { Free on a chained field receiver must nil the slot after the release —
      a stale pointer aliases the next allocation (UAF regression). }
    procedure TestFree_FieldReceiver_NilsSlot;
    { --debug-opdf facts: the backend emits per-statement .Ldbg labels and
      records exact frame offsets; normal builds stay label-free. }
    procedure TestOpdf_StatementLabels_AndFacts;
    procedure TestOpdf_Off_NoDbgLabels;
    { Self is typed as the owning class; value record params present the
      '_data' shadow slot (the inline copy) so field drilldown works. }
    procedure TestOpdf_Facts_SelfAndRecordParamTyping;
    { Regression: a float argument to an instance method must be marshalled
      into an SSE (xmm) argument register per the System V ABI, not an integer
      register.  Asserts the call site emits movsd into %xmm0. }
    procedure TestMethodFloatArg_LoadedIntoXmm;
    { Inline asm: a nostackframe asm-body function emits the verbatim block and
      NO compiler prologue (no pushq %rbp / frame subq). }
    procedure TestInlineAsm_VerbatimBody_NoPrologue;
    { Regression: an implicit-Self call whose Self+args exceed the six integer
      argument registers spills the overflow to the stack (it used to abort
      codegen).  Asserts the slot-block overflow shape and the dispatch. }
    procedure TestImplicitSelfCall_RegisterOverflow_Spills;
  end;

implementation

function TNativeConstArgTests.GenAsm(const ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenNative;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
    finally
      A.Free();
    end;
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(LinuxX64Target());
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

function TNativeConstArgTests.FuncRegion(const AAsm, AName: string): string;
var
  StartP, EndP: Integer;
begin
  StartP := Pos(AName + ':', AAsm);
  AssertTrue('function ' + AName + ' present in asm', StartP >= 0);
  EndP := StrPos('.type ' + AName, StrCopyTail(AAsm, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AAsm, StartP, EndP);
end;

function TNativeConstArgTests.CountOccurrences(const ANeedle,
  AHaystack: string): Integer;
var
  I: Integer;
begin
  Result := 0;
  I := Pos(ANeedle, AHaystack);
  while I >= 0 do
  begin
    Result := Result + 1;
    I := PosEx(ANeedle, AHaystack, I + 1);
  end;
end;

procedure TNativeConstArgTests.TestCallee_ConstStringParam_NoEntryExitPair;
const
  Src = '''
      program P;
      procedure SinkC(const S: string);
      begin
      end;
      begin
        SinkC('x')
      end.
      ''';
var
  Region: string;
begin
  { The callee must not retain/release a const string param — the caller
    protects the argument now (matches the QBE convention since 5a5b5d4). }
  Region := FuncRegion(GenAsm(Src), 'SinkC');
  AssertEquals('no entry AddRef in const-param callee', -1,
    Pos('_StringAddRef', Region));
  AssertEquals('no exit Release in const-param callee', -1,
    Pos('_StringRelease', Region));
end;

procedure TNativeConstArgTests.TestCallee_ValueStringParam_KeepsEntryExitPair;
const
  Src = '''
      program P;
      procedure SinkV(S: string);
      begin
      end;
      begin
        SinkV('x')
      end.
      ''';
var
  Region: string;
begin
  { Value string params keep the callee entry/exit pair — only const params
    moved to caller-side protection. }
  Region := FuncRegion(GenAsm(Src), 'SinkV');
  AssertTrue('entry AddRef kept for value param',
    Pos('_StringAddRef', Region) >= 0);
  AssertTrue('exit Release kept for value param',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_ParamForward_NoArcOps;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller(const T: string);
      begin
        Sink(T)
      end;
      var L: string;
      begin
        L := 'x';
        Caller(L)
      end.
      ''';
var
  Region: string;
begin
  { Forwarding a const param to a const param: borrowed all the way. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertEquals('no AddRef in Caller', -1, Pos('_StringAddRef', Region));
  AssertEquals('no Release in Caller', -1, Pos('_StringRelease', Region));
end;

procedure TNativeConstArgTests.TestConstArg_Literal_NoPin;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      begin
        Sink('hello')
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertEquals('no AddRef for literal arg', -1, Pos('_StringAddRef', Region));
  AssertEquals('no Release for literal arg', -1, Pos('_StringRelease', Region));
end;

procedure TNativeConstArgTests.TestConstArg_LocalVar_NoPin;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      function Mk: string;
      begin
        Result := IntToStr(7)
      end;
      procedure Caller;
      var
        L: string;
      begin
        L := Mk();
        Sink(L)
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { L := Mk() consumes the owned return; Sink(L) borrows L (no pin pair).
    The only releases allowed are the assignment release-old and L's
    scope-exit release — a pinned call would add a third. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertEquals('no AddRef in Caller', -1, Pos('_StringAddRef', Region));
  AssertTrue('at most two Releases (assign old + scope exit), no call pin',
    CountOccurrences('_StringRelease', Region) <= 2);
end;

procedure TNativeConstArgTests.TestConstArg_GlobalVar_Pins;
const
  Src = '''
      program P;
      var G: string;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      begin
        Sink(G)
      end;
      begin
        G := 'x';
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { A global can be reassigned by the callee through its own name — pin. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins global arg', Pos('_StringAddRef', Region) >= 0);
  AssertTrue('Release unpins global arg', Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_OwnedReturn_ConsumeOnly;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      function Mk: string;
      begin
        Result := IntToStr(7)
      end;
      procedure Caller;
      begin
        Sink(Mk())
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { Mk() hands over a +1 temp; the post-call release consumes it (without
    this the temp leaks — the callee no longer frees it for us). }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertEquals('no AddRef for owned-return arg', -1,
    Pos('_StringAddRef', Region));
  AssertTrue('Release consumes the owned temp',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_Concat_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller(const T: string);
      begin
        Sink('a' + T)
      end;
      var L: string;
      begin
        L := 'x';
        Caller(L)
      end.
      ''';
var
  Region: string;
begin
  { _StringConcat returns an rc=0 transient: the pin pair both protects it
    during the call and frees it afterwards. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins concat temp', Pos('_StringAddRef', Region) >= 0);
  AssertTrue('Release frees concat temp', Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_VarStringSibling_Pins;
const
  Src = '''
      program P;
      procedure Swapish(const A: string; var B: string);
      begin
        B := 'new'
      end;
      procedure Caller;
      var
        L: string;
      begin
        L := IntToStr(7);
        Swapish(L, L)
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { B aliases L: the callee's write to B releases L's buffer while A still
    borrows it — a var/out string sibling param forces a pin. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins despite local shape',
    Pos('_StringAddRef', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_AddrTakenLocal_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      var
        L: string;
        PS: ^string;
      begin
        L := IntToStr(7);
        PS := @L;
        Sink(L);
        PS^ := 'x'
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins address-taken local',
    Pos('_StringAddRef', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_CapturedLocal_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      var
        L: string;
        procedure Nested;
        begin
          L := 'changed'
        end;
      begin
        L := IntToStr(7);
        Sink(L);
        Nested()
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins captured local',
    Pos('_StringAddRef', Region) >= 0);
end;

procedure TNativeConstArgTests.TestConstArg_InterfaceDispatch_ConcatPins;
const
  Src = '''
      program P;
      type
        ISink = interface
          procedure Put(const S: string);
        end;
        TSink = class(TObject, ISink)
        public
          procedure Put(const S: string);
        end;
      procedure TSink.Put(const S: string);
      begin
      end;
      procedure Caller(V: ISink; const T: string);
      begin
        V.Put('a' + T)
      end;
      var
        O: TSink;
        I: ISink;
        L: string;
      begin
        O := TSink.Create();
        I := O;
        L := 'x';
        Caller(I, L)
      end.
      ''';
var
  Region: string;
begin
  { Interface dispatch cannot see the implementing method's const-ness, so
    the caller must protect every string argument by shape: the concat
    transient pins.  Without this, a const-param implementor receives an
    unprotected rc=0 transient. }
  Region := FuncRegion(GenAsm(Src), 'Caller');
  AssertTrue('AddRef pins concat temp at interface call site',
    Pos('_StringAddRef', Region) >= 0);
  AssertTrue('Release frees concat temp at interface call site',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeConstArgTests.TestFree_FieldReceiver_NilsSlot;
var
  Region: string;
begin
  Region := FuncRegion(GenAsm('''
      program P;
      type
        TInner = class
          N: Integer;
        end;
        TOuter = class
          Inner: TInner;
        end;
      procedure Drop(O: TOuter);
      begin
        O.Inner.Free();
      end;
      begin
      end.
      '''), 'Drop');
  AssertTrue('releases the field value',
    CountOccurrences('callq _ClassRelease', Region) >= 1);
  AssertTrue('nils the field slot after the release',
    CountOccurrences('movq $0, (%rdx)', Region) >= 1);
end;

procedure TNativeConstArgTests.TestOpdf_StatementLabels_AndFacts;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenNative;
  Asm_: string;
  F:    TDbgFunc;
  V:    TDbgVar;
begin
  L := TLexer.Create('''
      program P;
      function Twice(X: Integer): Integer;
      var H: Integer;
      begin
        H := X * 2;
        Result := H;
      end;
      begin
        WriteLn(Twice(4));
      end.
      ''');
  P := TParser.Create(L);
  Prog := P.Parse();
  P.Free(); L.Free();
  A := TSemanticAnalyser.Create();
  A.Analyse(Prog);
  A.Free();
  CG := TCodeGenNative.Create();
  CG.SetTarget(LinuxX64Target());
  CG.SetOpdfMode(True);
  CG.Generate(Prog);
  Asm_ := CG.GetOutput();
  AssertTrue('statement labels emitted', Pos('.Ldbg_0:', Asm_) > 0);
  AssertTrue('end label emitted', Pos('.Ldbg_end_', Asm_) > 0);
  AssertNotNil('facts collected', CG.GetDebugFacts());
  AssertEquals('two functions recorded (Twice + main)',
    2, CG.GetDebugFacts().Funcs.Count);
  F := TDbgFunc(CG.GetDebugFacts().Funcs.Items[0]);
  AssertEquals('symbol', 'Twice', F.SymbolName);
  AssertTrue('end label recorded', F.EndLabel <> '');
  V := F.FindVar('X');
  AssertNotNil('param X recorded', V);
  AssertTrue('X marked as param', V.IsParam);
  AssertEquals('X at first slot', -8, V.RbpOffset);
  V := F.FindVar('H');
  AssertNotNil('local H recorded', V);
  AssertTrue('H not a param', not V.IsParam);
  Prog.Free();
  CG.Free();
end;

procedure TNativeConstArgTests.TestOpdf_Off_NoDbgLabels;
var
  Asm_: string;
begin
  Asm_ := GenAsm('''
      program P;
      function Twice(X: Integer): Integer;
      begin
        Result := X * 2;
      end;
      begin
        WriteLn(Twice(4));
      end.
      ''');
  AssertTrue('no debug labels in a normal build', Pos('.Ldbg_', Asm_) < 0);
end;

procedure TNativeConstArgTests.TestOpdf_Facts_SelfAndRecordParamTyping;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenNative;
  F:    TDbgFunc;
  V:    TDbgVar;
  I:    Integer;
begin
  L := TLexer.Create('''
      program P;
      type
        TPt = record X, Y: Integer; end;
        TW = class
          N: Integer;
          procedure Track(Q: TPt);
        end;
      procedure TW.Track(Q: TPt);
      begin
        N := N + Q.X;
      end;
      var W: TW; G: TPt;
      begin
        W := TW.Create();
        W.Track(G);
      end.
      ''');
  P := TParser.Create(L);
  Prog := P.Parse();
  P.Free(); L.Free();
  A := TSemanticAnalyser.Create();
  A.Analyse(Prog);
  CG := TCodeGenNative.Create();
  CG.SetTarget(LinuxX64Target());
  CG.SetOpdfMode(True);
  CG.SetSymbolTable(Prog.SymbolTable);
  CG.Generate(Prog);
  A.Free();
  F := nil;
  for I := 0 to CG.GetDebugFacts().Funcs.Count - 1 do
    if TDbgFunc(CG.GetDebugFacts().Funcs.Items[I]).SymbolName = 'TW_Track' then
      F := TDbgFunc(CG.GetDebugFacts().Funcs.Items[I]);
  AssertNotNil('Track scope recorded', F);
  V := F.FindVar('Self');
  AssertNotNil('Self recorded', V);
  AssertNotNil('Self typed as the owning class', V.TypeDesc);
  AssertEquals('Self type', 'TW', V.TypeDesc.Name);
  V := F.FindVar('Q');
  AssertNotNil('record param recorded', V);
  AssertTrue('record param is a param', V.IsParam);
  AssertNotNil('record param typed', V.TypeDesc);
  AssertEquals('record param presents the inline copy type', 'TPt', V.TypeDesc.Name);
  AssertTrue('inline copy below the raw pointer slot', V.RbpOffset < -16);
  Prog.Free();
  CG.Free();
end;

procedure TNativeConstArgTests.TestMethodFloatArg_LoadedIntoXmm;
const
  Src = '''
      program P;
      type TX = class procedure Take(d: Double); end;
      procedure TX.Take(d: Double); begin end;
      var x: TX;
      begin
        x := TX.Create();
        x.Take(1.5)
      end.
      ''';
var
  AsmText: string;
begin
  AsmText := GenAsm(Src);
  { The Double argument must reach the SSE arg register, not an integer one. }
  AssertTrue('float method arg loaded into %xmm0',
    Pos('movsd', AsmText) >= 0);
  AssertTrue('float method arg targets the SSE arg register',
    Pos('%xmm0', AsmText) >= 0);
end;

procedure TNativeConstArgTests.TestInlineAsm_VerbatimBody_NoPrologue;
const
  Src = '''
      program P;
      function GetFortyTwo: Integer; assembler; nostackframe;
      asm
          movl $42, %eax
          ret
      end;
      begin
        WriteLn(GetFortyTwo())
      end.
      ''';
var
  AsmText: string;
  Region:  string;
begin
  AsmText := GenAsm(Src);
  Region := Self.FuncRegion(AsmText, 'GetFortyTwo');
  { The verbatim asm instructions appear in the function body. }
  AssertTrue('verbatim movl $42', Pos('movl $42, %eax', Region) >= 0);
  AssertTrue('verbatim ret', Pos('ret', Region) >= 0);
  { nostackframe: no compiler-emitted prologue inside the function. }
  AssertTrue('no pushq %rbp prologue', Pos('pushq %rbp', Region) < 0);
end;

procedure TNativeConstArgTests.TestImplicitSelfCall_RegisterOverflow_Spills;
const
  Src = '''
      program P;
      type
        TW = class
          function C(a, b, c, d, e, f, g: Integer): Integer;
          function D(): Integer;
        end;
      function TW.C(a, b, c, d, e, f, g: Integer): Integer;
      begin
        Result := a;
      end;
      function TW.D(): Integer;
      begin
        Result := C(1, 2, 3, 4, 5, 6, 7);
      end;
      begin
      end.
      ''';
var
  Region: string;
begin
  { Implicit-Self call C(...): Self (%rdi) + 7 args = 8 integer slots.  Six load
    into registers; the last two spill to the stack.  The slot-block overflow
    path stores Self into 0(%rsp) and fills all six integer arg registers —
    unlike the <=6 push/pop fast path.  Before the fix this aborted codegen with
    'arg register index 6 out of range'. }
  Region := FuncRegion(GenAsm(Src), 'TW_D');
  AssertTrue('overflow call dispatched', Pos('callq TW_C', Region) >= 0);
  AssertTrue('Self stored into slot 0 (overflow slot-block path)',
    Pos('movq %rax, 0(%rsp)', Region) >= 0);
  AssertTrue('arg registers filled through %r9',
    (Pos('%r8', Region) >= 0) and (Pos('%r9', Region) >= 0));
end;

initialization
  RegisterTest(TNativeConstArgTests);

end.
