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

initialization
  RegisterTest(TE2EThreadVarTests);

end.
