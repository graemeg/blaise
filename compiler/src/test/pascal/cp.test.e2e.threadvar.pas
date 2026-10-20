{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.threadvar;

{ E2E tests for threadvars of every type, through every consumer form: the
  TLS address must be used wherever the variable is read, written, resized,
  passed by reference or captured.  Each program runs on the host ISA (x86-64
  on Linux, arm64 on macOS).  On 2026-10-14 none of these shapes had a test:
  x86-64 miscompiled several (the static TLS template written instead of the
  thread's copy) and arm64 refused most of the types outright. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EThreadVarTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_DynArrayThreadVar_SetLengthAndElements;
    procedure TestRun_StringThreadVar_SetLengthAndDelete;
    procedure TestRun_SingleThreadVar;
    procedure TestRun_ManagedRecordThreadVar_CopyInAndOut;
    procedure TestRun_InterfaceThreadVar_AssignCallNil;
    procedure TestRun_ClassThreadVar_FreeNilsTheSlot;
    procedure TestRun_ThreadVar_AddressAndVarArg;
    procedure TestRun_ManagedStaticArrayThreadVar;
    procedure TestRun_ForInOverDynArrayThreadVar;
    procedure TestRun_ThreadVar_CapturedByClosure;
    procedure TestRun_RecordThreadVar_DynArrayField;
    procedure TestRun_RecordThreadVar_FromRecordReturningCall;
    procedure TestRun_ThreadVar_AsForInLoopVariable;
    procedure TestRun_ClosureThreadVar;
    procedure TestRun_InterfaceThreadVar_VarAndConstArgs;
    procedure TestRun_MethodPointerThreadVar;
    procedure TestRun_MetaclassThreadVar_VarArg;
    procedure TestRun_InitialisedIntegerThreadVar;
    procedure TestRun_InitialisedStringThreadVar;
    procedure TestRun_InitialisedThreadVar_EveryThreadStartsFromIt;
    procedure TestRun_InitialisedThreadVars_FloatBoolAndArray;
    procedure TestRun_ThreadVarsOfAUsedUnit;
    procedure TestRun_InitialisedThreadVars_DeclaredInUnit;
    procedure TestRun_ThreadExit_ReleasesEveryManagedKind;
    procedure TestRun_ThreadExit_ReleasesAReferenceItOnlyRetained;
    procedure TestRun_MainThreadVar_ReleasedAtProgramExit;
    procedure TestRun_ThreadExit_ReleasesAUsedUnitsThreadVar;
    procedure TestRun_InitialisedThreadVars_DynamicLink;
  end;

implementation

const
  LE = #10;

procedure TE2EThreadVarTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-threadvar');
end;

procedure TE2EThreadVarTests.TestRun_DynArrayThreadVar_SetLengthAndElements;
begin
  { SetLength on a dyn-array threadvar resized the TLS TEMPLATE on x86-64 (Length stayed 0 and the element store crashed); arm64 refused the type }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar A: array of Integer;
    begin SetLength(A, 3); A[1] := 7; A[2] := A[1] * 2; WriteLn(Length(A), ' ', A[1], ' ', A[2]); SetLength(A, 0); WriteLn(Length(A)); end.
    ''', '3 7 14' + LE + '0' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_StringThreadVar_SetLengthAndDelete;
begin
  { SetLength / Delete on a string threadvar were silently lost on x86-64 }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar S: string;
    begin S := 'hello'; SetLength(S, 4); WriteLn(S); Delete(S, 0, 1); WriteLn(S); end.
    ''', 'hell' + LE + 'ell' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_SingleThreadVar;
begin
  { arm64 refused a Single threadvar }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar F: Single;
    begin F := 1.5; F := F * 2; WriteLn(F:0:2); end.
    ''', '3.00' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ManagedRecordThreadVar_CopyInAndOut;
begin
  { a record threadvar with a managed field, copied in and out; arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TR = record S: string; N: Integer; end;
    threadvar R: TR;
    var L: TR;
    begin R.S := 'hi'; R.N := 4; WriteLn(R.S, R.N); L := R; L.S := L.S + '!'; WriteLn(L.S, ' ', R.S); R := L; WriteLn(R.S); end.
    ''', 'hi4' + LE + 'hi! hi' + LE + 'hi!' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InterfaceThreadVar_AssignCallNil;
begin
  { x86-64 gave an interface threadvar no _obj/_itab labels in .tbss (the program died); arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type
      IGreet = interface function Hi(): string; end;
      TGreet = class(IGreet) function Hi(): string; end;
    function TGreet.Hi(): string; begin Result := 'hi'; end;
    threadvar G: IGreet;
    begin G := TGreet.Create(); WriteLn(G.Hi()); WriteLn(G <> nil); G := nil; WriteLn(G = nil); end.
    ''', 'hi' + LE + 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ClassThreadVar_FreeNilsTheSlot;
begin
  { Free on a class threadvar cleared the static template slot on x86-64, not the thread's }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TC = class N: Integer; end;
    threadvar C: TC;
    begin C := TC.Create(); C.N := 9; WriteLn(C.N); C.Free(); WriteLn(C = nil); end.
    ''', '9' + LE + 'True' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadVar_AddressAndVarArg;
begin
  { @ and var-argument forms of a scalar threadvar }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar N: Integer;
    var P: ^Integer;
    procedure Bump(var X: Integer); begin X := X + 10; end;
    begin N := 1; P := @N; P^ := 2; WriteLn(N); Bump(N); WriteLn(N); end.
    ''', '2' + LE + '12' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ManagedStaticArrayThreadVar;
begin
  { a static array of strings as a threadvar; arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar A: array[0..3] of string;
    var I: Integer;
    begin for I := 0 to 3 do A[I] := IntToStr(I * I); WriteLn(A[0], A[1], A[2], A[3]); end.
    ''', '0149' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ForInOverDynArrayThreadVar;
begin
  { for-in over a dyn-array threadvar iterated nothing on x86-64 }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar A: array of Integer;
    var X, T: Integer;
    begin SetLength(A, 3); A[0] := 1; A[1] := 2; A[2] := 3; T := 0; for X in A do T := T + X; WriteLn(T); end.
    ''', '6' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadVar_CapturedByClosure;
begin
  { a closure updating a threadvar }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar N: Integer;
    var F: reference to procedure;
    begin N := 1; F := procedure begin N := N + 41; end; F(); WriteLn(N); end.
    ''', '42' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_RecordThreadVar_DynArrayField;
begin
  { SetLength on a dyn-array FIELD of a record threadvar }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TR = record A: array of Integer; end;
    threadvar R: TR;
    begin SetLength(R.A, 2); R.A[1] := 6; WriteLn(Length(R.A), R.A[1]); end.
    ''', '26' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_RecordThreadVar_FromRecordReturningCall;
begin
  { a record-returning call stored into a record threadvar (sret destination) }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TR = record S: string; A, B: Integer; end;
    threadvar R: TR;
    function Mk(const S: string; A, B: Integer): TR; begin Result.S := S; Result.A := A; Result.B := B; end;
    begin R := Mk('pq', 3, 4); WriteLn(R.S, ' ', R.A, ' ', R.B); end.
    ''', 'pq 3 4' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadVar_AsForInLoopVariable;
begin
  { a threadvar as the for-in loop variable }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar S: string;
    var L: array of string; Acc: string;
    begin SetLength(L, 2); L[0] := 'a'; L[1] := 'b'; Acc := ''; for S in L do Acc := Acc + S; WriteLn(Acc); end.
    ''', 'ab' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ClosureThreadVar;
begin
  { a closure threadvar: x86-64 called through leaq %fs:F@tpoff, the bare offset; arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar F: reference to function(X: Integer): Integer;
    threadvar K: Integer;
    begin K := 99; F := function(X: Integer): Integer begin Result := X + 4; end; WriteLn(F(3)); end.
    ''', '7' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InterfaceThreadVar_VarAndConstArgs;
begin
  { an interface threadvar filled through a var argument and read through a const one }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type
      IGreet = interface function Hi(): string; end;
      TGreet = class(IGreet) function Hi(): string; end;
    function TGreet.Hi(): string; begin Result := 'hi'; end;
    threadvar G: IGreet;
    threadvar After: Integer;
    procedure Fill(var X: IGreet); begin X := TGreet.Create(); end;
    procedure Show(const X: IGreet); begin WriteLn(X.Hi()); end;
    begin After := 0; Fill(G); WriteLn(G.Hi()); Show(G); end.
    ''', 'hi' + LE + 'hi' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_MethodPointerThreadVar;
begin
  { a method-pointer threadvar (16-byte Code+Data); arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TC = class N: Integer; function Get(): Integer; end;
      TGetter = function(): Integer of object;
    function TC.Get(): Integer; begin Result := N; end;
    threadvar M: TGetter;
    threadvar Guard: Integer;
    var C: TC;
    begin C := TC.Create(); C.N := 5; M := @C.Get; Guard := 1; WriteLn(M()); end.
    ''', '5' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_MetaclassThreadVar_VarArg;
begin
  { a metaclass threadvar and a metaclass global through a var argument; arm64 refused the threadvar }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TA = class end; TB = class(TA) end; TAClass = class of TA;
    threadvar M: TAClass;
    var G: TAClass;
    procedure Pick(var X: TAClass); begin X := TB; end;
    begin M := TA; WriteLn(M = TA); Pick(G); WriteLn(G = TB); Pick(M); WriteLn(M = TB); end.
    ''', 'True' + LE + 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedIntegerThreadVar;
begin
  { an initialised threadvar starts from its value: x86-64 dropped the initialiser (printed 0); arm64 refused it }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar N: Integer = 5;
    begin WriteLn(N); N := N + 1; WriteLn(N); end.
    ''', '5' + LE + '6' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedStringThreadVar;
begin
  { a string initialiser points at an immortal literal in the TLS image }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar S: string = 'abc';
    begin WriteLn(S); S := S + 'd'; WriteLn(S); end.
    ''', 'abc' + LE + 'abcd' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedThreadVar_EveryThreadStartsFromIt;
begin
  { every thread starts from the declared value, not only the main thread }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program tvprobe;
    uses Classes;
    threadvar N: Integer = 5;
    threadvar S: string;
    type TW = class(TThread) procedure Execute(); override; end;
    var Got: Integer; GotS: string;
    procedure TW.Execute(); begin Got := N; N := 99; S := 'w'; GotS := S; end;
    var T: TW;
    begin S := 'main'; T := TW.Create(False); T.WaitFor(); WriteLn(Got, ' ', N, ' ', GotS, ' ', S); end.
    ''', '5 5 w main' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedThreadVars_FloatBoolAndArray;
begin
  { initialisers of the other scalar kinds and of static arrays }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    threadvar
      D: Double = 2.5;
      B: Boolean = True;
      W: Word = 513;
      Q: Int64 = 1099511627776;
      A: array[0..2] of Integer = (4, 5, 6);
      T: array[0..1] of string = ('x', 'yz');
    begin WriteLn(D:0:1, ' ', B, ' ', W, ' ', Q, ' ', A[0] + A[1] + A[2], ' ', T[0], T[1]); A[1] := 0; WriteLn(A[0] + A[1] + A[2]); end.
    ''', '2.5 True 513 1099511627776 15 xyz' + LE + '10' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadVarsOfAUsedUnit;
const
  { threadvars a USED unit declares, reached from the program under separate
    compilation: arm64 referenced them as ordinary _g_ globals and the link
    failed ("undefined symbol _g_tvw_X"), for every type }
  UnitSrc = '''
    unit tvw;
    interface
    type
      IGreet = interface function Hi(): string; end;
      TGreet = class(IGreet) function Hi(): string; end;
    threadvar
      X: Integer;
      S: string;
      G: IGreet;
    implementation
    function TGreet.Hi(): string; begin Result := 'hi' end;
    end.
    ''';
  ProgSrc = '''
    program P;
    uses tvw;
    begin
      X := 3;
      S := 'ab';
      G := TGreet.Create();
      WriteLn(X, S, G.Hi());
      G := nil;
      S := ''
    end.
    ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + Output,
    CompileAndRunWithUnitNative('tvw', UnitSrc, ProgSrc, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '3abhi' + LE, Output);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedThreadVars_DeclaredInUnit;
const
  { a unit's initialised threadvars, interface and implementation section,
    reach the program through separate compilation }
  UnitSrc = '''
    unit tvu;
    interface
    threadvar
      Counter: Integer = 40;
      Tag: string = 'u';
    function Bump(): Integer;
    implementation
    threadvar
      Step: Integer = 2;
    function Bump(): Integer;
    begin
      Counter := Counter + Step;
      Result := Counter
    end;
    end.
    ''';
  ProgSrc = '''
    program P;
    uses tvu;
    begin
      WriteLn(Bump(), ' ', Tag);
      WriteLn(Counter)
    end.
    ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + Output,
    CompileAndRunWithUnitNative('tvu', UnitSrc, ProgSrc, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '42 u' + LE + '42' + LE, Output);
end;

procedure TE2EThreadVarTests.TestRun_ThreadExit_ReleasesEveryManagedKind;
begin
  { a worker's managed threadvars are released when it exits -- class,
    interface, record field, dyn-array element and closure env.  Nothing
    released them, on either backend: the count was 0.  The thread is
    started AFTER T holds it: started from the constructor (Create(False)),
    the closure's conservatively captured Self could take the instance
    0 -> 1 -> 0 and free it before the constructor returned (~10% under
    load) -- BUG-20261020-thread-exit-flaky-segv, fixed by making a
    constructor call return an owned reference; restore Create(False) then. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program tvprobe;
    uses Classes;
    type
      TNoisy = class destructor Destroy; override; end;
      IGreet = interface function Hi(): string; end;
      TGreet = class(IGreet) function Hi(): string; destructor Destroy; override; end;
      TRec = record O: TNoisy; N: Integer; end;
      TProc = reference to procedure;
    var Freed: Integer;
    destructor TNoisy.Destroy; begin Freed := Freed + 1 end;
    function TGreet.Hi(): string; begin Result := 'hi' end;
    destructor TGreet.Destroy; begin Freed := Freed + 1 end;
    threadvar
      C: TNoisy; G: IGreet; R: TRec; A: array of TNoisy; P: TProc;
    type TW = class(TThread) procedure Execute(); override; end;
    procedure TW.Execute();
    var Cap: TNoisy;
    begin
      C := TNoisy.Create();
      G := TGreet.Create();
      R.O := TNoisy.Create();
      SetLength(A, 1);
      A[0] := TNoisy.Create();
      Cap := TNoisy.Create();
      P := procedure begin Cap.Free() end;
    end;
    var T: TW;
    begin T := TW.Create(True); T.Start(); T.WaitFor(); WriteLn(Freed); end.
    ''', '5' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadExit_ReleasesAReferenceItOnlyRetained;
begin
  { the worker only RETAINS a shared object (no allocation of its own), and
    its [Weak] and [Unretained] threadvars own nothing: the object dies when
    main drops the last reference, not before and not never }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program tvprobe;
    uses Classes;
    type
      TNoisy = class destructor Destroy; override; end;
      TW = class(TThread) procedure Execute(); override; end;
    destructor TNoisy.Destroy; begin WriteLn('freed') end;
    threadvar
      Held: TNoisy;
      [Weak] W: TNoisy;
      [Unretained] U: TNoisy;
    var Shared: TNoisy;
    procedure TW.Execute(); begin Held := Shared; W := Shared; U := Shared; end;
    var T: TW;
    begin
      Shared := TNoisy.Create();
      T := TW.Create(False); T.WaitFor();
      WriteLn('joined'); Shared := nil; WriteLn('dropped');
    end.
    ''', 'joined' + LE + 'freed' + LE + 'dropped' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_MainThreadVar_ReleasedAtProgramExit;
begin
  { the main thread ends with exit(), not a thread exit: its copies are
    released at program end like the globals }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program tvprobe;
    type TNoisy = class destructor Destroy; override; end;
    destructor TNoisy.Destroy; begin WriteLn('freed') end;
    threadvar C: TNoisy;
    begin C := TNoisy.Create(); WriteLn('end') end.
    ''', 'end' + LE + 'freed' + LE, 0);
end;

procedure TE2EThreadVarTests.TestRun_ThreadExit_ReleasesAUsedUnitsThreadVar;
const
  { the threadvar and its finaliser live in the unit's object; the
    program's worker arms the unit's node }
  UnitSrc = '''
    unit tvx;
    interface
    type TNoisy = class destructor Destroy; override; end;
    threadvar Held: TNoisy;
    var Freed: Integer;
    implementation
    destructor TNoisy.Destroy; begin Freed := Freed + 1 end;
    end.
    ''';
  ProgSrc = '''
    program P;
    uses Classes, tvx;
    type TW = class(TThread) procedure Execute(); override; end;
    procedure TW.Execute(); begin Held := TNoisy.Create() end;
    var T: TW;
    begin T := TW.Create(False); T.WaitFor(); WriteLn(Freed) end.
    ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + Output,
    CompileAndRunWithUnitNative('tvx', UnitSrc, ProgSrc, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '1' + LE, Output);
end;

procedure TE2EThreadVarTests.TestRun_InitialisedThreadVars_DynamicLink;
const
  { a dynamic ELF image never carried the TLS initialisation image: .tdata
    was placed past the data PT_LOAD, so every thread started from zeros
    (and the copy ran off the end of the linker's buffer).  The other tests
    link Linux programs freestanding; this one forces the libc link. }
  Src = '''
    program tvprobe;
    threadvar
      N: Integer = 40;
      S: string = 'u';
      M: Integer = 2;
    begin WriteLn(N + M, ' ', S) end.
    ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run: ' + Output,
    CompileAndRun(Src, Output, RCode, ['--dynamic']));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '42 u' + LE, Output);
end;

initialization
  RegisterTest(TE2EThreadVarTests);

end.
