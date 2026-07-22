{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.nativearc;

{ Assembly-level ARC tests for the NATIVE x86-64 backend.

  These cannot live in cp.test.arc.pas: that unit's uses clause pulls in
  blaise.codegen.qbe only, and its GenIR helper drives the QBE emitter — the
  QBE backend has a single cleanup routine (EmitArcCleanup) driven by
  Block.Decls, so it cannot see a native-only gap.

  The native x86-64 backend has TWO hand-written ARC cleanup paths: the
  procedure-frame walk (driven by the method's Body.Decls) and the main-body
  walk EmitGlobalReleases (driven by FDataGlobals, since PROGRAM-level vars
  are registered as globals).  A gap in one is invisible to the other, so the
  main-body path needs its own assertions. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.target;

type
  TNativeArcTests = class(TTestCase)
  private
    function GenAsm(const ASrc: string): string;
    function MainExitRegion(const AAsm: string): string;
  published
    { A PROGRAM-level static array of managed elements is a GLOBAL, so its
      cleanup runs through EmitGlobalReleases, not the procedure-frame walk.
      That kind chain handled string/class/dyn-array/interface/record but not
      tyStaticArray, so every element leaked at program exit on native while
      QBE was correct. }
    procedure TestMain_ProgramStaticArrayOfClass_EmitsClassRelease;
    procedure TestMain_ProgramStaticArrayOfString_EmitsStringRelease;
    procedure TestMain_ProgramStaticArrayOfRecord_EmitsStringRelease;
    { An unmanaged element type must emit no release walk at all. }
    procedure TestMain_ProgramStaticArrayOfInteger_NoReleases;
    { The pre-existing scalar-global arms must keep working. }
    procedure TestMain_ProgramClassGlobal_EmitsClassRelease;
    { A record whose ONLY managed content is a static-array-of-managed field
      must take the ARC copy path on `B := A` (retain source elements before
      the memcpy).  RecretManagedClean lacked a tyStaticArray case, so such a
      record was mis-classified as managed-clean and copied by bare memcpy —
      both sides then shared the refs and the scope-exit walk double-released
      (BUG-20260721-recretclean-static-array-of-managed). }
    procedure TestMain_RecordCopy_StaticArrayOfStringOnly_EmitsRetain;
  end;

implementation

function TNativeArcTests.GenAsm(const ASrc: string): string;
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
      CG.SetTarget(HostTarget());
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

{ Slice the main-body EPILOGUE — everything from the .Lmain_exitN label to the
  end of main.  Slicing the whole of main would be useless: the body itself
  emits _ClassRelease/_StringRelease for ordinary assignments and transients,
  so a whole-main assertion passes vacuously whether or not the exit cleanup
  exists.  The global ARC releases are emitted only after the exit label. }
function TNativeArcTests.MainExitRegion(const AAsm: string): string;
var
  StartP, EndP, MainP: Integer;
  Tail: string;
begin
  MainP := Pos('main:', AAsm);
  AssertTrue('main present in asm', MainP >= 0);
  Tail := StrCopyTail(AAsm, MainP);
  EndP := StrPos('.type main', Tail);
  AssertTrue('main closed', EndP >= 0);
  Tail := StrCopyFrom(AAsm, MainP, EndP);
  StartP := Pos('.Lmain_exit', Tail);
  AssertTrue('main exit label present', StartP >= 0);
  Result := StrCopyTail(Tail, StartP);
end;

const
  SrcProgArrayOfClass = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
      end;
    var
      A: array[0..2] of TObjX;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := TObjX.Create();
      WriteLn(A[2].Tag);
    end.
    ''';

  SrcProgArrayOfString = '''
    program P;
    var
      A: array[0..2] of string;
      I: Integer;
    begin
      for I := 0 to 2 do
        A[I] := 'x';
      WriteLn(A[2]);
    end.
    ''';

  SrcProgArrayOfRecord = '''
    program P;
    type
      TRecX = record
        Name: string;
      end;
    var
      A: array[0..2] of TRecX;
    begin
      A[0].Name := 'x';
      WriteLn(A[0].Name);
    end.
    ''';

  SrcProgArrayOfInteger = '''
    program P;
    var
      A: array[0..2] of Integer;
    begin
      A[0] := 7;
      WriteLn(A[0]);
    end.
    ''';

  SrcProgClassGlobal = '''
    program P;
    type
      TObjX = class
      public
        Tag: Integer;
      end;
    var
      G: TObjX;
    begin
      G := TObjX.Create();
      WriteLn(G.Tag);
    end.
    ''';

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfClass_EmitsClassRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(Self.GenAsm(SrcProgArrayOfClass));
  AssertTrue('main releases the program-level array elements, got: ' + Region,
    Pos('_ClassRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfString_EmitsStringRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(Self.GenAsm(SrcProgArrayOfString));
  AssertTrue('main releases the program-level string array elements',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfRecord_EmitsStringRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(Self.GenAsm(SrcProgArrayOfRecord));
  AssertTrue('main recurses into record elements'' managed fields',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_ProgramStaticArrayOfInteger_NoReleases;
var
  Region: string;
begin
  Region := Self.MainExitRegion(Self.GenAsm(SrcProgArrayOfInteger));
  AssertTrue('unmanaged element type emits no release walk',
    (Pos('_ClassRelease', Region) < 0) and (Pos('_StringRelease', Region) < 0));
end;

procedure TNativeArcTests.TestMain_ProgramClassGlobal_EmitsClassRelease;
var
  Region: string;
begin
  Region := Self.MainExitRegion(Self.GenAsm(SrcProgClassGlobal));
  AssertTrue('scalar class global still released at main exit',
    Pos('_ClassRelease', Region) >= 0);
end;

procedure TNativeArcTests.TestMain_RecordCopy_StaticArrayOfStringOnly_EmitsRetain;
var
  Asm_: string;
begin
  { The copy `B := A` is the only statement, so a retain anywhere in the
    output can only come from the ARC record-copy path (the scope-exit walk
    emits releases only). }
  Asm_ := Self.GenAsm(
    '''
    program P;
    type
      TR = record
        Arr: array[0..1] of string;
      end;
    var
      A, B: TR;
    begin
      B := A;
      WriteLn(1);
    end.
    ''');
  AssertTrue('record copy retains static-array-of-string elements',
    Pos('_StringAddRef', Asm_) >= 0);
end;

initialization
  RegisterTest(TNativeArcTests);

end.
