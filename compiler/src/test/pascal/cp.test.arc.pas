{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.arc;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, cp.test.harness;

type
  TARCTests = class(TTestCase)
  private
    function IRContains(const AIR, AFragment: string): Boolean;
    function CountSubstring(const AHaystack, ANeedle: string): Integer;
    function FuncRegion(const AIR, AHeader: string): string;
  published
    { const and var parameters borrow: the callee takes no reference }
    procedure TestCodegen_ConstAndVarParams_TakeNoReference;
    { String variable assignment inserts retain before release }

    { Block exit releases all string variables }

    { Integer assignment has no ARC calls }

    { WriteLn of string literal still works }

    { String variable passed to WriteLn (load + _SysWriteStr) }

    { String value parameter: addref on entry, release on exit }

    { Dyn-array value parameter: addref on entry, release on exit — a
      dyn-array is a ref-counted pointer, so the callee's co-owning copy
      must be counted (BUG-20260721-byval-dynarray-param-no-arc). }

    { String var parameter: no addref, no release }

    { String const parameter: callee skips the addref/release pair (5a5b5d4
      elision — the caller keeps a named argument alive for the whole call). }

    { Caller-side retain when a transient (concat result, +0 rc) is passed
      to a routine with a const-string parameter.  The callee no longer
      retains under the 5a5b5d4 elision, so the call site must keep the
      buffer alive for the call duration. }

    { Interface const parameter: callee skips the addref/release pair too. }

    { Interface value parameter: addref on entry, release on exit (via the
      obj slot — interfaces ARC through _ClassAddRef/_ClassRelease). }

    { Interface var parameter: no addref, no release in the callee. }

    { String concatenation: calls RTL concat function }
    procedure TestARC_StringConcat_SemanticOK;

    { Destroy as destructor hook: field cleanup fn invokes it }

    { Nil-slot release elision: first store to a class-typed local in the
      function entry block must skip _ClassRelease (slot is provably nil
      from EmitVarAllocs). }

    { Pointer-to-class coercion: assigning a Pointer-typed expression to a
      class-typed variable must emit _ClassAddRef (the LHS is ARC-managed). }

    { Return-value ownership transfer: a string/dyn-array function result
      already owns +1, so assigning it to a variable must NOT emit a second
      AddRef (that spurious retain leaks one buffer per call).  Assigning a
      plain variable (borrowed) still retains. }

    { Pointer-write ARC (BUG-012 part 2): storing through a typed pointer
      (`P^ := V`) is the primitive every generic container uses for its
      element slots.  It retained strings and class refs but silently
      dropped interfaces and dyn-arrays, making TList<IFoo> NON-OWNING —
      a use-after-free hazard, not merely a leak. }

    { Pointer-READ ARC (BUG-012 part 3): `G := P^` through a ^IFoo is the
      counterpart of the write above — the read side of every generic
      container's element slot.  The slot is a 16-byte fat pointer, so both
      words must be loaded from the address and the obj half retained. }

    { A[I].Free() on a static-array element must release AND nil the element
      slot, like the identifier/field receiver forms — a stale pointer left
      in the slot double-frees under the scope-exit ARC walk (BUG-016). }

    { BUG-016 stage 1: the array element STORE's retain must be conditional
      on RHS ownership (ArcExprOwnsRef), mirroring scalar assignment and the
      arm64 backend.  An owned +1 RHS (call result) transfers its reference;
      a borrowed RHS (plain variable) still retains. }

    { BUG-016 stage 2: static-array-of-managed LOCALS are released at scope
      exit (previously interface elements only).  The normal path must NOT
      zero the slots (AZero=False); only the exception-path walk zeroes. }

    { BUG-017: a static-array-of-managed FIELD of a record must be retained
      on record copy / value-param entry and released by the field walks —
      retain + copy + release land together or record copies over/under-
      release. }
    { Discarded calls to sret-returning functions must pass a hidden result
      buffer and release the discarded result's managed content
      (BUG-20260722-discarded-sret-call-no-buffer). }
    { BUG-20260922-record-closure-field-not-managed: a 'reference to' field
      makes a record "managed clean" — the env half at +8 is never released,
      the record is register-returned, and a whole-record copy shares the env
      with no retain.  A plain / 'of object' procedural field stays UNmanaged
      (its Data half is a bare code pointer / borrowed receiver). }
    { A method-backed property setter BORROWS its value: an owned-transient
      string value (concat / function result) must be disposed by the
      caller after the setter call
      (BUG-20260721-propsetter-owned-transient-str-leak). }
    { Same contract through the DEFAULT array property write (Obj[I] := V),
      which lowers through EmitStaticSubscriptAssign, not
      EmitFieldAssignment (BUG-20260721-propsetter-owned-transient-str-leak). }
  end;

implementation

function TARCTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

function TARCTests.CountSubstring(const AHaystack, ANeedle: string): Integer;
var
  Found: Integer;
  Tail:  string;
begin
  Result := 0;
  if (ANeedle = '') or (AHaystack = '') then
    Exit;
  Tail := AHaystack;
  while True do
  begin
    { Pos here follows the surrounding test-file convention (>0 = found).
      For a 0-based interpretation we'd use >=0; either way a needle that
      starts at index 0 is exceedingly unlikely against IR text. }
    Found := Pos(ANeedle, Tail);
    if Found <= 0 then break;
    Result := Result + 1;
    { Move past this match.  Copy/Length here are 1-based to match the
      Pos convention used above. }
    Tail := Copy(Tail, Found + Length(ANeedle),
                 Length(Tail) - (Found + Length(ANeedle)) + 1);
    if Tail = '' then break;
  end;
end;

const
  SrcConcat =
    '''
        program P;
        var a, b, c: string;
        begin
          c := a + b
        end.
        ''';

function TARCTests.FuncRegion(const AIR, AHeader: string): string;
var
  P, E: Integer;
  Tail: string;
begin
  { Slice one emitted function: from its header line to the closing brace.
    Whole-IR assertions would pass vacuously off the caller's own ARC. }
  P := Pos(AHeader, AIR);
  AssertTrue(AHeader + ' present', P >= 0);
  Tail := Copy(AIR, P, Length(AIR) - P);
  E := Pos(#10 + '}', Tail);
  AssertTrue(AHeader + ' closed', E >= 0);
  Result := Copy(Tail, 0, E);
end;

function ExtractDoSomethingBody(const AIR: string): string;
var
  FnPos, NextPos: Integer;
begin
  FnPos := Pos('function $DoSomething', AIR);
  if FnPos = 0 then Exit('');
  { Slice to the start of the next function definition (or end of IR). }
  NextPos := Pos('function ', Copy(AIR, FnPos + 20, Length(AIR)));
  if NextPos = 0 then
    Result := Copy(AIR, FnPos, Length(AIR) - FnPos + 1)
  else
    Result := Copy(AIR, FnPos, NextPos + 19);
end;

procedure TARCTests.TestARC_StringConcat_SemanticOK;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(SrcConcat);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
    AssertTrue('semantic analysis completed without error', True);
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Destroy as destructor hook                                          }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------ }
{ Return-value ownership transfer (string / dyn-array)                }
{ ------------------------------------------------------------------ }

const
function CallerBody(const AIR: string): string;
var
  P: Integer;
begin
  { Return the IR of the Run procedure (the caller), excluding the callee
    Make whose own AddRef/Release calls would confuse the assertion. }
  P := Pos('function $Run', AIR);
  if P <= 0 then
    P := Pos('$Run(', AIR);
  if P <= 0 then
    Exit(AIR);
  Result := Copy(AIR, P, Length(AIR) - P + 1);
end;

const
  { `P^ := V` through a ^IFoo — the shape generic containers use for an
    interface element slot. }
  SrcPointerWriteIntf = '''
      program P;
      type
        IFoo = interface
          procedure Bar;
        end;
        TFoo = class(IFoo)
          procedure Bar; begin end;
        end;
      procedure DoIt;
      var
        P: ^IFoo;
        V: IFoo;
      begin
        P := GetMem(16);
        V := TFoo.Create();
        P^ := V;
        FreeMem(P)
      end;
      begin
        DoIt()
      end.
      ''';

procedure TARCTests.TestCodegen_ConstAndVarParams_TakeNoReference;
const
  Src = '''
    program P;
    type
      TArr = array of Integer;
      IFoo = interface function Val: Integer; end;
    procedure SC(const S: string); begin WriteLn(Length(S)) end;
    procedure SV(var S: string); begin WriteLn(Length(S)) end;
    procedure DC(const A: TArr); begin WriteLn(Length(A)) end;
    procedure IC(const I: IFoo); begin WriteLn(I.Val()) end;
    procedure IV(var I: IFoo); begin WriteLn(I.Val()) end;
    procedure SB(S: string); begin WriteLn(Length(S)) end;
    begin end.
    ''';
var
  T, Name, AsmText, Body: string;
  I, J, P, E: Integer;
  Names: array[0..5] of string;
begin
  { A const or var parameter is borrowed: an extra retain/release pair in the
    callee would balance, so a running program cannot see it.  SB, a by-value
    string, is the control -- it does take its own reference. }
  Names[0] := 'SC'; Names[1] := 'SV'; Names[2] := 'DC';
  Names[3] := 'IC'; Names[4] := 'IV'; Names[5] := 'SB';
  for I := 0 to 1 do
  begin
    if I = 0 then T := TargetX86_64 else T := TargetArm64;
    AsmText := GenAsm(Src, T);
    for J := 0 to 5 do
    begin
      if I = 0 then Name := #10 + Names[J] + ':'
      else Name := #10 + '_' + Names[J] + ':';
      P := Pos(Name, AsmText);
      AssertTrue(T + ': ' + Names[J] + ' emitted', P >= 0);
      Body := Copy(AsmText, P, Length(AsmText) - P);
      E := Pos(#9 + 'ret', Body);
      Body := Copy(Body, 0, E);
      if J = 5 then
        AssertTrue(T + ': by-value control takes a reference',
          Pos('StringAddRef', Body) >= 0)
      else
        AssertTrue(T + ': ' + Names[J] + ' takes no reference',
          (Pos('AddRef', Body) < 0) and (Pos('Release', Body) < 0));
    end;
  end;
end;

initialization
  RegisterTest(TARCTests);

end.
