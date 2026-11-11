{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit cp.test.win64;

{ Windows milestone M2: the Win64 convention at the foreign boundary and
  stack probes (windows-x86_64-backend-design.adoc, "ABI design").

  A foreign call reserves one block below the stack pointer: the outgoing
  area at the bottom (32 bytes of home space, then the stack-passed
  arguments), one 8-byte temporary per argument above it, and the copies of
  records passed by reference above those.  Each argument is evaluated into
  its temporary first, then moved to where the convention puts it, so the
  assertions below name those offsets.

  The behaviour is checked in the Windows guest by scripts/windows-vm.sh
  crosscheck, which runs the programs TWin64FixtureTests links. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness,
  blaise.linker.pe, blaise.pereader, blaise.elfreader,
  blaise.assembler.x86_64, blaise.codegen.toolkit;

type
  TWin64CallTests = class(TTestCase)
  private
    function WinAsm(const ASrc: string): string;
    function WinError(const ASrc: string): string;
    procedure AssertHas(const AAsm, ALine: string);
    procedure AssertLacks(const AAsm, ALine: string);
  published
    { Integer arguments: RCX, RDX, R8, R9, then the stack above the home
      space. }
    procedure TestFourIntegerArgs_InRcxRdxR8R9;
    procedure TestFifthArg_OnStackAboveHomeSpace;
    { Positional assignment: a float takes the XMM register of its
      position, and an integer after it still takes its own position's
      register. }
    procedure TestMixedArgs_Positional;
    { A float in the variadic part is also passed in the integer register. }
    procedure TestVariadicFloat_MirroredToIntegerRegister;
    { A var parameter is its address, in an integer register. }
    procedure TestVarParam_AddressInIntegerRegister;
    { Records: 1, 2, 4 and 8 bytes travel as their bytes; any other size as
      the address of a copy. }
    procedure TestRecord8_ByValueInRegister;
    procedure TestRecord12_ByReferenceToCopy;
    { Which calls are foreign (D6). }
    procedure TestLibraryLessExternal_KeepsInternalConvention;
    procedure TestCdeclExternal_IsForeign;
    procedure TestLinux_ExternalLibCall_StaysSystemV;
    { Not lowered yet: an aggregate result from a foreign routine, and a
      routine with a body that foreign code calls (M5). }
    procedure TestRecordResult_FromForeignRoutine_IsAnError;
    procedure TestCdeclRoutineWithBody_IsAnError;
    { Stack probes: on Windows no single adjustment of %rsp spans a page. }
    procedure TestLargeFrame_ProbedOnWindows;
    procedure TestLargeFrame_NotProbedOnLinux;
  end;

  { The M2 program under test, compiled for windows-x86_64 and linked with
    the stand-in runtime; scripts/windows-vm.sh crosscheck runs the result
    in the guest. }
  TWin64FixtureTests = class(TTestCase)
  published
    procedure TestLink_M2Calls;
  end;

implementation

const
  NL = #10;
  Win = 'windows-x86_64';

{ ---- helpers ---- }

function TWin64CallTests.WinAsm(const ASrc: string): string;
begin
  Result := GenAsm(ASrc, Win);
end;

function TWin64CallTests.WinError(const ASrc: string): string;
begin
  Result := '';
  try
    GenAsm(ASrc, Win);
  except
    on E: Exception do
      Result := E.Message;
  end;
end;

procedure TWin64CallTests.AssertHas(const AAsm, ALine: string);
begin
  AssertTrue('expected [' + ALine + ']', Pos(ALine, AAsm) >= 0);
end;

procedure TWin64CallTests.AssertLacks(const AAsm, ALine: string);
begin
  AssertTrue('unexpected [' + ALine + ']', Pos(ALine, AAsm) < 0);
end;

{ The largest immediate of any `subq $N, %rsp` in AAsm. }
function LargestRspReserve(const AAsm: string): Int;
var
  L: TStringList;
  I, P, Q, V: Int;
  S: string;
begin
  Result := 0;
  L := TStringList.Create();
  try
    L.Text := AAsm;
    for I := 0 to L.Count - 1 do
    begin
      S := Trim(L.Strings[I]);
      if Copy(S, 0, 6) <> 'subq $' then Continue;
      Q := Pos(', %rsp', S);
      if Q < 0 then Continue;
      P := 6;
      V := StrToIntDef(Copy(S, P, Q - P), 0);
      if V > Result then Result := V;
    end;
  finally
    L.Free();
  end;
end;

{ ---- calls ---- }

procedure TWin64CallTests.TestFourIntegerArgs_InRcxRdxR8R9;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'function F(A, B, C, D: Int64): Int64; external ''k32'' name ''F'';' + NL +
    'var R: Int64;' + NL +
    'begin R := F(11, 22, 33, 44); end.');
  AssertHas(A, #9'subq $64, %rsp');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
  AssertHas(A, #9'movq 40(%rsp), %rdx');
  AssertHas(A, #9'movq 48(%rsp), %r8');
  AssertHas(A, #9'movq 56(%rsp), %r9');
  AssertHas(A, #9'callq F');
  AssertLacks(A, 'popq %rdi');
  AssertLacks(A, '%rax, %rdi');
end;

procedure TWin64CallTests.TestFifthArg_OnStackAboveHomeSpace;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'function F(A, B, C, D, E: Int64): Int64; external ''k32'' name ''F'';' + NL +
    'var R: Int64;' + NL +
    'begin R := F(1, 2, 3, 4, 5); end.');
  { outgoing 40 (home + one slot), five temporaries from 40 }
  AssertHas(A, #9'movq 72(%rsp), %rax' + NL + #9'movq %rax, 32(%rsp)');
  AssertHas(A, #9'movq 40(%rsp), %rcx');
  AssertHas(A, #9'movq 64(%rsp), %r9');
end;

procedure TWin64CallTests.TestMixedArgs_Positional;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'procedure G(A: Float64; B: Int32; C: Float32; D: Int64); external ''k32'' name ''G'';' + NL +
    'begin G(1.5, 7, 2.5, 9); end.');
  AssertHas(A, #9'movsd 32(%rsp), %xmm0');
  AssertHas(A, #9'movq 40(%rsp), %rdx');
  AssertHas(A, #9'movss 48(%rsp), %xmm2');
  AssertHas(A, #9'movq 56(%rsp), %r9');
  AssertLacks(A, '%xmm1');
end;

procedure TWin64CallTests.TestVariadicFloat_MirroredToIntegerRegister;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'function PF(Fmt: PChar): Int32; varargs; external ''msvcrt'' name ''printf'';' + NL +
    'begin PF(PChar(''%f''), 1.5); end.');
  AssertHas(A, #9'movsd 40(%rsp), %xmm1');
  AssertHas(A, #9'movq 40(%rsp), %rdx');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
end;

procedure TWin64CallTests.TestVarParam_AddressInIntegerRegister;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'procedure Q(var X: Float64); external ''k32'' name ''Q'';' + NL +
    'var D: Float64;' + NL +
    'begin Q(D); end.');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
  AssertLacks(A, '%xmm0');
end;

procedure TWin64CallTests.TestRecord8_ByValueInRegister;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'type TPt = record X, Y: Int32; end;' + NL +
    'procedure R(P: TPt); external ''k32'' name ''R'';' + NL +
    'var V: TPt;' + NL +
    'begin R(V); end.');
  { the record's eight bytes, not its address }
  AssertHas(A, #9'movq 0(%rcx), %rax' + NL + #9'movq %rax, 32(%rsp)');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
end;

procedure TWin64CallTests.TestRecord12_ByReferenceToCopy;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'type T3 = record X, Y, Z: Int32; end;' + NL +
    'procedure R(P: T3); external ''k32'' name ''R'';' + NL +
    'var V: T3;' + NL +
    'begin R(V); end.');
  { the copy sits above the one temporary; its address is the argument }
  AssertHas(A, #9'movq %rax, 40(%rsp)');
  AssertHas(A, #9'movl 8(%rcx), %eax' + NL + #9'movq %rax, 48(%rsp)');
  AssertHas(A, #9'leaq 40(%rsp), %rax' + NL + #9'movq %rax, 32(%rsp)');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
end;

procedure TWin64CallTests.TestLibraryLessExternal_KeepsInternalConvention;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'procedure H(A: Int64); external name ''H'';' + NL +
    'begin H(5); end.');
  AssertHas(A, #9'movq %rax, %rdi');
  AssertLacks(A, #9'movq 32(%rsp), %rcx');
end;

procedure TWin64CallTests.TestCdeclExternal_IsForeign;
var
  A: string;
begin
  A := WinAsm(
    'program p;' + NL +
    'procedure H(A: Int64); cdecl; external name ''H'';' + NL +
    'begin H(5); end.');
  AssertHas(A, #9'movq 32(%rsp), %rcx');
  AssertLacks(A, '%rax, %rdi');
end;

procedure TWin64CallTests.TestLinux_ExternalLibCall_StaysSystemV;
var
  A: string;
begin
  A := GenAsm(
    'program p;' + NL +
    'function F(A, B, C, D: Int64): Int64; external ''k32'' name ''F'';' + NL +
    'var R: Int64;' + NL +
    'begin R := F(11, 22, 33, 44); end.', 'linux-x86_64');
  AssertHas(A, 'popq %rdi');
  AssertLacks(A, #9'movq 32(%rsp), %rcx');
end;

procedure TWin64CallTests.TestRecordResult_FromForeignRoutine_IsAnError;
var
  Msg: string;
begin
  Msg := WinError(
    'program p;' + NL +
    'type TPt = record X, Y: Int32; end;' + NL +
    'function R: TPt; external ''k32'' name ''R'';' + NL +
    'var V: TPt;' + NL +
    'begin V := R(); end.');
  AssertTrue('names the routine and the restriction: ' + Msg,
    (Pos('R', Msg) >= 0) and (Pos('foreign routine', Msg) >= 0));
end;

procedure TWin64CallTests.TestCdeclRoutineWithBody_IsAnError;
var
  Msg: string;
begin
  Msg := WinError(
    'program p;' + NL +
    'function CB(A: Int32): Int32; cdecl;' + NL +
    'begin Result := A; end;' + NL +
    'begin CB(1); end.');
  AssertTrue('names the routine and the missing foreign entry: ' + Msg,
    (Pos('CB', Msg) >= 0) and (Pos('foreign entry', Msg) >= 0));
end;

{ ---- stack probes ---- }

const
  BigFrameSrc =
    'program p;' + NL +
    'procedure Big;' + NL +
    'var A: array[0..9999] of Byte;' + NL +
    'begin A[0] := 1; A[9999] := A[0]; end;' + NL +
    'begin Big(); end.';

procedure TWin64CallTests.TestLargeFrame_ProbedOnWindows;
var
  A: string;
begin
  A := WinAsm(BigFrameSrc);
  AssertHas(A, #9'subq $4096, %rsp' + NL + #9'orq $0, (%rsp)');
  AssertTrue('no adjustment spans a page',
    LargestRspReserve(A) <= 4096);
end;

procedure TWin64CallTests.TestLargeFrame_NotProbedOnLinux;
var
  A: string;
begin
  A := GenAsm(BigFrameSrc, 'linux-x86_64');
  AssertLacks(A, 'orq $0, (%rsp)');
  AssertTrue('one adjustment for the whole frame',
    LargestRspReserve(A) >= 10000);
end;

{ ---- fixtures ---- }

function ReadText(const APath: string): string;
var
  L: TStringList;
begin
  L := TStringList.Create();
  try
    L.LoadFromFile(APath);
    Result := L.Text;
  finally
    L.Free();
  end;
end;

procedure TWin64FixtureTests.TestLink_M2Calls;
var
  Root, Dir, OutDir: string;
  Lk: TPeLinker;
  Tk: TWindowsX86_64Toolkit;
  Img: TPeImage;
  I: Int;
  Dlls: string;
begin
  Root := GetCurrentDir();
  while (Root <> '') and
        not FileExists(Root + '/compiler/src/it/windows/m2calls.pas') do
    Root := ExtractFileDir(Root);
  AssertTrue('fixture found', Root <> '');
  Dir := Root + '/compiler/src/it/windows/';
  OutDir := Root + '/compiler/target/it/windows';
  ForceDirectories(OutDir);
  Tk := TWindowsX86_64Toolkit.Create();
  Lk := TPeLinker.Create();
  try
    Lk.DllNameOf := @Tk.LibraryImageName;
    Lk.AddObject(ParseElfObject(AssembleToBytes(
      GenAsm(ReadText(Dir + 'm2calls.pas'), Win)), 'm2calls.o'));
    Lk.AddObject(ParseElfObject(AssembleToBytes(ReadText(Dir + 'm2rt.s')),
      'm2rt.o'));
    Lk.LinkToFile('_start', OutDir + '/m2calls.exe');
  finally
    Lk.Free();
    Tk.Free();
  end;
  Img := ReadPeImageFile(OutDir + '/m2calls.exe');
  try
    Dlls := '';
    for I := 0 to Img.Imports.Count - 1 do
      Dlls := Dlls + Img.Imports[I].Dll + ' ';
    AssertEquals('kernel32.dll msvcrt.dll ', Dlls);
  finally
    Img.Free();
  end;
end;

initialization
  RegisterTest(TWin64CallTests);
  RegisterTest(TWin64FixtureTests);

end.
