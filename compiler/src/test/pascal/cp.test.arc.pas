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
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe;

type
  TARCTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
    function CountSubstring(const AHaystack, ANeedle: string): Integer;
  published
    { String variable assignment inserts retain before release }
    procedure TestARC_StringAssign_CallsRetain;
    procedure TestARC_StringAssign_CallsRelease;
    procedure TestARC_StringAssign_RetainBeforeRelease;

    { Block exit releases all string variables }
    procedure TestARC_StringVar_BlockExitRelease;
    procedure TestARC_TwoStringVars_BothReleasedAtExit;

    { Integer assignment has no ARC calls }
    procedure TestARC_IntAssign_NoRetain;
    procedure TestARC_IntAssign_NoRelease;

    { WriteLn of string literal still works }
    procedure TestARC_WriteLn_StringLit_StillWorks;

    { String variable passed to WriteLn (load + _SysWriteStr) }
    procedure TestARC_WriteLn_StringVar_Works;

    { String value parameter: addref on entry, release on exit }
    procedure TestARC_StringValueParam_AddRefOnEntry;
    procedure TestARC_StringValueParam_ReleaseOnExit;

    { String var parameter: no addref, no release }
    procedure TestARC_StringVarParam_NoAddRef;
    procedure TestARC_StringVarParam_NoRelease;

    { String const parameter: callee skips the addref/release pair (5a5b5d4
      elision — the caller keeps a named argument alive for the whole call). }
    procedure TestARC_StringConstParam_NoAddRef;
    procedure TestARC_StringConstParam_NoRelease;

    { Caller-side retain when a transient (concat result, +0 rc) is passed
      to a routine with a const-string parameter.  The callee no longer
      retains under the 5a5b5d4 elision, so the call site must keep the
      buffer alive for the call duration. }
    procedure TestARC_StringConstParam_CallerRetainsTransient_AddRef;
    procedure TestARC_StringConstParam_CallerRetainsTransient_Release;

    { Interface const parameter: callee skips the addref/release pair too. }
    procedure TestARC_IntfConstParam_NoAddRef;

    { Interface value parameter: addref on entry, release on exit (via the
      obj slot — interfaces ARC through _ClassAddRef/_ClassRelease). }
    procedure TestARC_IntfValueParam_AddRefOnEntry;
    procedure TestARC_IntfValueParam_ReleaseOnExit;

    { Interface var parameter: no addref, no release in the callee. }
    procedure TestARC_IntfVarParam_NoAddRef;

    { String concatenation: calls RTL concat function }
    procedure TestARC_StringConcat_SemanticOK;
    procedure TestARC_StringConcat_CallsRTL;

    { Destroy as destructor hook: field cleanup fn invokes it }
    procedure TestARC_ClassDestroy_FieldCleanupCallsIt;
    procedure TestARC_ClassWithoutDestroy_FieldCleanupNoCall;
    procedure TestARC_GenericClass_Destroy_FieldCleanupCallsIt;

    { Nil-slot release elision: first store to a class-typed local in the
      function entry block must skip _ClassRelease (slot is provably nil
      from EmitVarAllocs). }
    procedure TestARC_FirstClassAssign_ElidesRelease;
    procedure TestARC_SecondClassAssign_StillReleases;
    procedure TestARC_ClassAssign_AfterBranch_StillReleases;

    { Pointer-to-class coercion: assigning a Pointer-typed expression to a
      class-typed variable must emit _ClassAddRef (the LHS is ARC-managed). }
    procedure TestARC_PointerToClass_AssignEmitsAddRef;

    { Return-value ownership transfer: a string/dyn-array function result
      already owns +1, so assigning it to a variable must NOT emit a second
      AddRef (that spurious retain leaks one buffer per call).  Assigning a
      plain variable (borrowed) still retains. }
    procedure TestARC_StringAssignFromCall_NoSpuriousAddRef;
    procedure TestARC_StringAssignFromVar_StillAddRef;
    procedure TestARC_DynArrayAssignFromCall_NoSpuriousAddRef;
    procedure TestARC_DynArrayAssignFromVar_StillAddRef;

    { Pointer-write ARC (BUG-012 part 2): storing through a typed pointer
      (`P^ := V`) is the primitive every generic container uses for its
      element slots.  It retained strings and class refs but silently
      dropped interfaces and dyn-arrays, making TList<IFoo> NON-OWNING —
      a use-after-free hazard, not merely a leak. }
    procedure TestARC_PointerWrite_Interface_RetainsAndStoresItab;
    procedure TestARC_PointerWrite_DynArray_RetainsAndReleases;

    { Pointer-READ ARC (BUG-012 part 3): `G := P^` through a ^IFoo is the
      counterpart of the write above — the read side of every generic
      container's element slot.  The slot is a 16-byte fat pointer, so both
      words must be loaded from the address and the obj half retained. }
    procedure TestARC_PointerRead_Interface_LoadsBothSlotsAndRetains;

    { A[I].Free() on a static-array element must release AND nil the element
      slot, like the identifier/field receiver forms — a stale pointer left
      in the slot double-frees under the scope-exit ARC walk (BUG-016). }
    procedure TestARC_StaticArrayElemFree_NilsSlot;

    { BUG-016 stage 1: the array element STORE's retain must be conditional
      on RHS ownership (ArcExprOwnsRef), mirroring scalar assignment and the
      arm64 backend.  An owned +1 RHS (call result) transfers its reference;
      a borrowed RHS (plain variable) still retains. }
    procedure TestARC_StaticArrayElem_OwnedClassRhs_NoRetain;
    procedure TestARC_StaticArrayElem_BorrowedClassRhs_Retains;
    procedure TestARC_StaticArrayElem_OwnedStringRhs_NoRetain;
    procedure TestARC_StaticArrayElem_BorrowedStringRhs_Retains;
    procedure TestARC_DynArrayElem_OwnedClassRhs_NoRetain;
    procedure TestARC_DynArrayElem_BorrowedClassRhs_Retains;
    procedure TestARC_FieldElemStore_OwnedStringRhs_NoRetain;

    { BUG-016 stage 2: static-array-of-managed LOCALS are released at scope
      exit (previously interface elements only).  The normal path must NOT
      zero the slots (AZero=False); only the exception-path walk zeroes. }
    procedure TestARC_StaticArrayOfClass_BlockExitRelease;
    procedure TestARC_StaticArrayOfString_BlockExitRelease;
    procedure TestARC_StaticArrayOfRecord_BlockExitRelease;
    procedure TestARC_StaticArrayBlockExitRelease_DoesNotZeroSlots;

    { BUG-017: a static-array-of-managed FIELD of a record must be retained
      on record copy / value-param entry and released by the field walks —
      retain + copy + release land together or record copies over/under-
      release. }
    procedure TestARC_RecordWithStaticArrayField_ReleaseFields;
    procedure TestARC_RecordWithStaticArrayField_AddRefFields;
    procedure TestARC_RecordCopy_StaticArrayField_RetainsElements;
    procedure TestARC_RecordReturn_StaticArrayOnly_IsSret;
  end;

implementation

function TARCTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

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

{ ------------------------------------------------------------------ }

procedure TARCTests.TestARC_StringAssign_CallsRetain;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var s: string;
        begin
          s := 'hello'
        end.
        ''');
  AssertTrue('retain call present', IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StringAssign_CallsRelease;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var s: string;
        begin
          s := 'hello'
        end.
        ''');
  AssertTrue('release call present', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StringAssign_RetainBeforeRelease;
var
  IR:     string;
  PosTain, PosLease: Integer;
begin
  IR := GenIR(
    '''
        program P;
        var s: string;
        begin
          s := 'hello'
        end.
        ''');
  PosTain  := Pos('call $_StringAddRef', IR);
  PosLease := Pos('call $_StringRelease', IR);
  AssertTrue('retain before first release', PosTain < PosLease);
end;

procedure TARCTests.TestARC_StringVar_BlockExitRelease;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var s: string;
        begin end.
        ''');
  AssertTrue('release at block exit', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_TwoStringVars_BothReleasedAtExit;
var
  IR:    string;
  Count: Integer;
  Pos1, Pos2: Integer;
begin
  IR := GenIR(
    '''
        program P;
        var a, b: string;
        begin end.
        ''');
  { Two string vars → two release calls at exit.
    Use PosEx to count all occurrences (0-based index; -1 = not found). }
  Count := 0;
  Pos1  := 0;
  repeat
    Pos1 := PosEx('call $_StringRelease', IR, Pos1);
    if Pos1 < 0 then Break;
    Inc(Count);
    Inc(Pos1);
  until False;
  AssertTrue('at least 2 releases', Count >= 2);
end;

procedure TARCTests.TestARC_IntAssign_NoRetain;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var n: Integer;
        begin
          n := 42
        end.
        ''');
  AssertFalse('no retain for int', IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_IntAssign_NoRelease;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var n: Integer;
        begin
          n := 42
        end.
        ''');
  AssertFalse('no release for int', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_WriteLn_StringLit_StillWorks;
var
  IR: string;
begin
  IR := GenIR('program P; begin WriteLn(''Hello'') end.');
  AssertTrue('_SysWriteStr called', IRContains(IR, 'call $_SysWriteStr'));
  AssertTrue('data section present', IRContains(IR, 'data $__s0'));
end;

procedure TARCTests.TestARC_WriteLn_StringVar_Works;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var s: string;
        begin
          s := 'world';
          WriteLn(s)
        end.
        ''');
  AssertTrue('_SysWriteStr called', IRContains(IR, 'call $_SysWriteStr'));
end;

const
  SrcValParam =
    '''
        program P;
        procedure Greet(S: string);
        begin end;
        begin end.
        ''';

  SrcVarParam =
    '''
        program P;
        procedure Greet(var S: string);
        begin end;
        begin end.
        ''';

  SrcConstParam =
    '''
        program P;
        procedure Greet(const S: string);
        begin end;
        begin end.
        ''';

  { Concat result (rc=0 +0 transient) passed to a const-string parameter.
    The body of Greet calls another const-string routine to force at least
    one ARC event against the borrowed buffer; without the caller-side
    retain inserted by EnsureConstStringRef, that event drives the
    transient's refcount negative. }
  SrcConstParamTransient =
    '''
        program P;
        procedure Inner(const T: string);
        begin end;
        procedure Greet(const S: string);
        begin
          Inner(S)
        end;
        begin
          Greet('foo' + 'bar')
        end.
        ''';

  SrcIntfConstParam =
    '''
        program P;
        type
          IThing = interface
            procedure Emit;
          end;
          TThing = class(TObject, IThing)
            procedure Emit;
          end;
        procedure TThing.Emit;
        begin end;
        procedure DoSomething(const MyIntf: IThing);
        begin
          MyIntf.Emit()
        end;
        var T: TThing; F: IThing;
        begin
          T := TThing.Create();
          F := T;
          DoSomething(F)
        end.
        ''';

  SrcIntfValueParam =
    '''
        program P;
        type
          IThing = interface
            procedure Emit;
          end;
          TThing = class(TObject, IThing)
            procedure Emit;
          end;
        procedure TThing.Emit;
        begin end;
        procedure DoSomething(MyIntf: IThing);
        begin
          MyIntf.Emit()
        end;
        var T: TThing; F: IThing;
        begin
          T := TThing.Create();
          F := T;
          DoSomething(F)
        end.
        ''';

  SrcIntfVarParam =
    '''
        program P;
        type
          IThing = interface
            procedure Emit;
          end;
          TThing = class(TObject, IThing)
            procedure Emit;
          end;
        procedure TThing.Emit;
        begin end;
        procedure DoSomething(var MyIntf: IThing);
        begin
          MyIntf.Emit()
        end;
        var T: TThing; F: IThing;
        begin
          T := TThing.Create();
          F := T;
          DoSomething(F)
        end.
        ''';

  SrcConcat =
    '''
        program P;
        var a, b, c: string;
        begin
          c := a + b
        end.
        ''';

procedure TARCTests.TestARC_StringValueParam_AddRefOnEntry;
var
  IR: string;
begin
  IR := GenIR(SrcValParam);
  AssertTrue('addref for string value param', IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StringValueParam_ReleaseOnExit;
var
  IR: string;
begin
  IR := GenIR(SrcValParam);
  AssertTrue('release for string value param', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StringVarParam_NoAddRef;
var
  IR: string;
begin
  IR := GenIR(SrcVarParam);
  AssertFalse('no addref for string var param', IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StringVarParam_NoRelease;
var
  IR: string;
begin
  IR := GenIR(SrcVarParam);
  AssertFalse('no release for string var param', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StringConstParam_NoAddRef;
var
  IR: string;
begin
  IR := GenIR(SrcConstParam);
  AssertFalse('no addref for string const param', IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StringConstParam_NoRelease;
var
  IR: string;
begin
  IR := GenIR(SrcConstParam);
  AssertFalse('no release for string const param', IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StringConstParam_CallerRetainsTransient_AddRef;
var
  IR: string;
begin
  IR := GenIR(SrcConstParamTransient);
  AssertTrue('caller retains transient before const-string call',
    IRContains(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StringConstParam_CallerRetainsTransient_Release;
var
  IR: string;
begin
  IR := GenIR(SrcConstParamTransient);
  AssertTrue('caller releases transient after const-string call',
    IRContains(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_IntfConstParam_NoAddRef;
var
  Body: string;
begin
  Body := ExtractDoSomethingBody(GenIR(SrcIntfConstParam));
  AssertTrue('DoSomething emitted', Body <> '');
  AssertFalse('no addref for interface const param',
    Pos('call $_ClassAddRef', Body) > 0);
  AssertFalse('no release for interface const param',
    Pos('call $_ClassRelease', Body) > 0);
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

procedure TARCTests.TestARC_IntfValueParam_AddRefOnEntry;
var
  Body: string;
begin
  Body := ExtractDoSomethingBody(GenIR(SrcIntfValueParam));
  AssertTrue('DoSomething emitted', Body <> '');
  AssertTrue('addref for interface value param',
    Pos('call $_ClassAddRef', Body) > 0);
end;

procedure TARCTests.TestARC_IntfValueParam_ReleaseOnExit;
var
  Body: string;
begin
  Body := ExtractDoSomethingBody(GenIR(SrcIntfValueParam));
  AssertTrue('DoSomething emitted', Body <> '');
  AssertTrue('release for interface value param',
    Pos('call $_ClassRelease', Body) > 0);
end;

procedure TARCTests.TestARC_IntfVarParam_NoAddRef;
var
  Body: string;
begin
  Body := ExtractDoSomethingBody(GenIR(SrcIntfVarParam));
  AssertTrue('DoSomething emitted', Body <> '');
  AssertFalse('no addref for interface var param',
    Pos('call $_ClassAddRef', Body) > 0);
  AssertFalse('no release for interface var param',
    Pos('call $_ClassRelease', Body) > 0);
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

procedure TARCTests.TestARC_StringConcat_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcConcat);
  AssertTrue('string concat calls RTL', IRContains(IR, '$_StringConcat'));
end;

{ ------------------------------------------------------------------ }
{ Destroy as destructor hook                                          }
{ ------------------------------------------------------------------ }

const
  SrcDestroyClass =
    '''
        program P;
        type
          TBuf = class
            FData: ^Integer;
            procedure Destroy;
          end;
        procedure TBuf.Destroy;
        begin
          FreeMem(Self.FData)
        end;
        var B: TBuf;
        begin
          B := TBuf.Create()
        end.
        ''';

  SrcNoDestroyClass =
    '''
        program P;
        type
          TFoo = class
            V: Integer;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create()
        end.
        ''';

  SrcGenericDestroy =
    '''
        program P;
        type
          TBox<T> = class
            FData: ^T;
            procedure Destroy;
          end;
        procedure TBox<T>.Destroy;
        begin
          FreeMem(Self.FData)
        end;
        var B: TBox<Integer>;
        begin
          B := TBox<Integer>.Create()
        end.
        ''';

procedure TARCTests.TestARC_ClassDestroy_FieldCleanupCallsIt;
var
  IR: string;
begin
  IR := GenIR(SrcDestroyClass);
  AssertTrue('field cleanup function calls Destroy',
    IRContains(IR, 'call $TBuf_Destroy'));
end;

procedure TARCTests.TestARC_ClassWithoutDestroy_FieldCleanupNoCall;
var
  IR: string;
begin
  IR := GenIR(SrcNoDestroyClass);
  AssertFalse('no Destroy call when method absent',
    IRContains(IR, 'call $TFoo_Destroy'));
end;

procedure TARCTests.TestARC_GenericClass_Destroy_FieldCleanupCallsIt;
var
  IR: string;
begin
  IR := GenIR(SrcGenericDestroy);
  AssertTrue('monomorphized field cleanup calls Destroy',
    IRContains(IR, 'call $TBox_Integer_Destroy'));
end;

procedure TARCTests.TestARC_FirstClassAssign_ElidesRelease;
var
  IR:      string;
  FnPos:   Integer;
  FnBody:  string;
begin
  { First class-typed assignment to a local in the function entry block:
    the slot was just zeroed by EmitVarAllocs, so _ClassRelease(nil) is
    elided. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        procedure DoIt;
        var f: TFoo;
        begin
          f := TFoo.Create()
        end;
        begin
          DoIt()
        end.
        ''');
  FnPos := Pos('function $DoIt', IR);
  AssertTrue('DoIt function emitted', FnPos > 0);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  AssertTrue('first store calls AddRef',
    Pos('call $_ClassAddRef', FnBody) > 0);
  { Block-exit release of f is still emitted, but the first-assignment
    release must NOT appear before the block-exit one.  Exactly one
    _ClassRelease in DoIt is the expected post-elision count. }
  AssertEquals('exactly one _ClassRelease in DoIt',
    1, CountSubstring(FnBody, 'call $_ClassRelease'));
end;

procedure TARCTests.TestARC_SecondClassAssign_StillReleases;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  { Two assignments to the same local class slot.  The first elides
    release (nil slot); the second must release the prior value or we
    leak. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        procedure DoIt;
        var f: TFoo;
        begin
          f := TFoo.Create();
          f := TFoo.Create()
        end;
        begin
          DoIt()
        end.
        ''');
  FnPos  := Pos('function $DoIt', IR);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  { 2nd assign + block-exit cleanup = 2 _ClassRelease. }
  AssertEquals('two _ClassRelease in DoIt (2nd assign + block exit)',
    2, CountSubstring(FnBody, 'call $_ClassRelease'));
end;

procedure TARCTests.TestARC_ClassAssign_AfterBranch_StillReleases;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  { An assignment after an if-branch is conservatively treated as
    "not provably nil" and must emit the release. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        procedure DoIt;
        var f: TFoo; c: Boolean;
        begin
          c := True;
          if c then
            f := TFoo.Create();
          f := TFoo.Create()
        end;
        begin
          DoIt()
        end.
        ''');
  FnPos  := Pos('function $DoIt', IR);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  { Post-branch assign + block-exit cleanup → at least 2.
    The inside-branch assign may itself be elided since it was in a
    branch that started before the slot was written. }
  AssertTrue('at least two _ClassRelease (post-branch + block exit)',
    CountSubstring(FnBody, 'call $_ClassRelease') >= 2);
end;

procedure TARCTests.TestARC_PointerToClass_AssignEmitsAddRef;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  { A function returning TObject is declared as returning Pointer externally,
    then stored into a TObject local.  The assignment codegen must see the
    LHS type (tyClass) and emit _ClassAddRef even though the RHS resolved
    type is tyPointer.  Without the fix the Pointer→class coercion path
    falls through to a plain storel, causing an imbalanced _ClassRelease at
    scope exit. }
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        function GetPtr: Pointer; external name 'GetPtr';
        procedure DoIt;
        var
          F: TFoo;
          P: Pointer;
        begin
          P := GetPtr();
          F := TFoo(P)
        end;
        begin
          DoIt()
        end.
        ''');
  FnPos  := Pos('function $DoIt', IR);
  AssertTrue('DoIt function emitted', FnPos > 0);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  AssertTrue('Pointer-to-class assign emits _ClassAddRef',
    Pos('call $_ClassAddRef', FnBody) > 0);
end;

{ ------------------------------------------------------------------ }
{ Return-value ownership transfer (string / dyn-array)                }
{ ------------------------------------------------------------------ }

const
  { Caller does `r := Make()` where Make returns a string.  Make's Result
    already owns +1, so the assignment must NOT AddRef again.  The callee
    Make emits its own _StringAddRef calls, so the assertion scopes to the
    caller (Run) function body. }
  SrcStringAssignFromCall =
    '''
        program P;
        function Make: string;
        begin
          Result := 'x'
        end;
        procedure Run;
        var r: string;
        begin
          r := Make()
        end;
        begin
          Run()
        end.
        ''';

  { Caller does `b := a` between two string variables.  `a` is borrowed, so
    the assignment MUST AddRef. }
  SrcStringAssignFromVar =
    '''
        program P;
        procedure Run;
        var a, b: string;
        begin
          a := 'x';
          b := a
        end;
        begin
          Run()
        end.
        ''';

  SrcDynArrayAssignFromCall =
    '''
        program P;
        type TIntArr = array of Integer;
        function Make: TIntArr;
        var a: TIntArr;
        begin
          SetLength(a, 1);
          Result := a
        end;
        procedure Run;
        var r: TIntArr;
        begin
          r := Make()
        end;
        begin
          Run()
        end.
        ''';

  SrcDynArrayAssignFromVar =
    '''
        program P;
        type TIntArr = array of Integer;
        procedure Run;
        var a, b: TIntArr;
        begin
          SetLength(a, 1);
          b := a
        end;
        begin
          Run()
        end.
        ''';

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

procedure TARCTests.TestARC_StringAssignFromCall_NoSpuriousAddRef;
var
  Body: string;
begin
  Body := CallerBody(GenIR(SrcStringAssignFromCall));
  AssertTrue('string call-result assignment does not AddRef the transient',
    Pos('call $_StringAddRef', Body) <= 0);
  AssertTrue('old slot is still released',
    Pos('call $_StringRelease', Body) > 0);
end;

procedure TARCTests.TestARC_StringAssignFromVar_StillAddRef;
var
  Body: string;
begin
  Body := CallerBody(GenIR(SrcStringAssignFromVar));
  AssertTrue('borrowed string variable assignment still AddRefs',
    Pos('call $_StringAddRef', Body) > 0);
end;

procedure TARCTests.TestARC_DynArrayAssignFromCall_NoSpuriousAddRef;
var
  Body: string;
begin
  Body := CallerBody(GenIR(SrcDynArrayAssignFromCall));
  AssertTrue('dyn-array call-result assignment does not AddRef the transient',
    Pos('call $_DynArrayAddRef', Body) <= 0);
  AssertTrue('old slot is still released',
    Pos('call $_DynArrayRelease', Body) > 0);
end;

procedure TARCTests.TestARC_DynArrayAssignFromVar_StillAddRef;
var
  Body: string;
begin
  Body := CallerBody(GenIR(SrcDynArrayAssignFromVar));
  AssertTrue('borrowed dyn-array variable assignment still AddRefs',
    Pos('call $_DynArrayAddRef', Body) > 0);
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

  SrcPointerWriteDynArray = '''
      program P;
      type
        TArr = array of Integer;
      procedure DoIt;
      var
        P: ^TArr;
        V: TArr;
      begin
        P := GetMem(8);
        SetLength(V, 3);
        P^ := V;
        FreeMem(P)
      end;
      begin
        DoIt()
      end.
      ''';

procedure TARCTests.TestARC_PointerWrite_Interface_RetainsAndStoresItab;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  IR     := GenIR(SrcPointerWriteIntf);
  FnPos  := Pos('function $DoIt', IR);
  AssertTrue('DoIt function emitted', FnPos > 0);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  { The interface fat pointer is 16 bytes: obj at +0 (refcounted through
    _ClassAddRef/_ClassRelease) and itab at +8 (static rodata, copied raw).
    Two AddRef/Release pairs appear in the body: one for `V := TFoo.Create()`
    and one for the pointer write, so require at least two of each. }
  AssertTrue('pointer write retains the interface obj',
    CountSubstring(FnBody, 'call $_ClassAddRef') >= 2);
  AssertTrue('pointer write releases the old interface obj',
    CountSubstring(FnBody, 'call $_ClassRelease') >= 2);
  AssertTrue('pointer write stores the itab slot at +8',
    Pos('add %_t', FnBody) > 0);
end;

procedure TARCTests.TestARC_PointerWrite_DynArray_RetainsAndReleases;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  IR     := GenIR(SrcPointerWriteDynArray);
  FnPos  := Pos('function $DoIt', IR);
  AssertTrue('DoIt function emitted', FnPos > 0);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  AssertTrue('pointer write retains the dyn-array',
    Pos('call $_DynArrayAddRef', FnBody) > 0);
  { One release for the pointer write's old slot, one at scope exit for V. }
  AssertTrue('pointer write releases the old dyn-array',
    CountSubstring(FnBody, 'call $_DynArrayRelease') >= 2);
end;

const
  { `G := P^` through a ^IFoo — the read counterpart of SrcPointerWriteIntf. }
  SrcPointerReadIntf = '''
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
        G: IFoo;
      begin
        P := GetMem(16);
        ZeroMem(P, 16);
        V := TFoo.Create();
        P^ := V;
        G := P^;
        FreeMem(P)
      end;
      begin
        DoIt()
      end.
      ''';

procedure TARCTests.TestARC_PointerRead_Interface_LoadsBothSlotsAndRetains;
var
  IR:     string;
  FnPos:  Integer;
  FnBody: string;
begin
  IR     := GenIR(SrcPointerReadIntf);
  FnPos  := Pos('function $DoIt', IR);
  AssertTrue('DoIt function emitted', FnPos > 0);
  FnBody := Copy(IR, FnPos, Length(IR) - FnPos + 1);
  { Three AddRef sites now: `V := TFoo.Create()`, the pointer write `P^ := V`
    and the pointer read `G := P^`.  Before the fix the read emitted a bare
    scalar load with no retain (and on the QBE side a dangling reference to
    the destination symbol), so requiring three pins the new arm. }
  AssertTrue('pointer read retains the interface obj it loaded',
    CountSubstring(FnBody, 'call $_ClassAddRef') >= 3);
  AssertTrue('pointer read releases the destination''s prior obj',
    CountSubstring(FnBody, 'call $_ClassRelease') >= 3);
end;

const
  { Static-array element receives an OWNED +1 class RHS (user-function call
    result).  ArcExprOwnsRef(MakeC()) is True, so the element store must NOT
    retain — the transferred reference is consumed by the slot.  The only
    remaining _ClassAddRef is the `Result := TC.Create()` inside MakeC. }
  SrcSAElemOwnedClass = '''
      program P;
      type
        TC = class
        public
          X: Integer;
        end;
      function MakeC(): TC;
      begin
        Result := TC.Create();
      end;
      procedure Run();
      var
        A: array[0..1] of TC;
      begin
        A[0] := MakeC();
      end;
      begin
        Run();
      end.
      ''';

  { Borrowed class RHS (plain variable): the element store MUST retain.
    Two _ClassAddRef sites: the `B := TC.Create()` constructor-assign and
    the element store.  Also the shape for the block-exit release test:
    after BUG-016 stage 2 the scope-exit walk releases both elements. }
  SrcSAElemBorrowedClass = '''
      program P;
      type
        TC = class
        public
          X: Integer;
        end;
      procedure Run();
      var
        A: array[0..1] of TC;
        B: TC;
      begin
        B := TC.Create();
        A[0] := B;
      end;
      begin
        Run();
      end.
      ''';

  SrcSAElemOwnedString = '''
      program P;
      function MakeS(): string;
      begin
        Result := 'x';
      end;
      procedure Run();
      var
        A: array[0..1] of string;
      begin
        A[0] := MakeS();
      end;
      begin
        Run();
      end.
      ''';

  SrcSAElemBorrowedString = '''
      program P;
      procedure Run();
      var
        A: array[0..1] of string;
        B: string;
      begin
        B := 'x';
        A[0] := B;
      end;
      begin
        Run();
      end.
      ''';

  SrcDynElemOwnedClass = '''
      program P;
      type
        TC = class
        public
          X: Integer;
        end;
      function MakeC(): TC;
      begin
        Result := TC.Create();
      end;
      procedure Run();
      var
        D: array of TC;
      begin
        SetLength(D, 2);
        D[0] := MakeC();
      end;
      begin
        Run();
      end.
      ''';

  SrcDynElemBorrowedClass = '''
      program P;
      type
        TC = class
        public
          X: Integer;
        end;
      procedure Run();
      var
        D: array of TC;
        B: TC;
      begin
        SetLength(D, 2);
        B := TC.Create();
        D[0] := B;
      end;
      begin
        Run();
      end.
      ''';

  { Element store into an array-typed FIELD (B.Names[0] := MakeS()) routes
    through the field-elem-store path, which must apply the same conditional
    retain.  One _StringAddRef remains (inside MakeS). }
  SrcFieldElemOwnedString = '''
      program P;
      type
        TBox = class
        public
          Names: array[0..1] of string;
        end;
      function MakeS(): string;
      begin
        Result := 'x';
      end;
      procedure Run();
      var
        B: TBox;
      begin
        B := TBox.Create();
        B.Names[0] := MakeS();
        B.Free();
      end;
      begin
        Run();
      end.
      ''';

  { Static-array-of-RECORD local: the scope-exit walk recurses array ->
    record -> string field. }
  SrcSAOfRecord = '''
      program P;
      type
        TR = record
          S: string;
        end;
      procedure Run();
      var
        A: array[0..1] of TR;
        R: TR;
      begin
        R.S := 'x';
        A[0] := R;
      end;
      begin
        Run();
      end.
      ''';

  { Record with a static-array-of-string FIELD (BUG-017 shapes). }
  SrcRecArrayField = '''
      program P;
      type
        TR = record
          Names: array[0..1] of string;
        end;
      procedure Run();
      var
        R: TR;
      begin
        R.Names[0] := 'x';
      end;
      begin
        Run();
      end.
      ''';

  SrcRecArrayFieldByValParam = '''
      program P;
      type
        TR = record
          Names: array[0..1] of string;
        end;
      procedure Show(R: TR);
      begin
      end;
      procedure Run();
      var
        R: TR;
      begin
        R.Names[0] := 'x';
        Show(R);
      end;
      begin
        Run();
      end.
      ''';

  SrcRecArrayFieldCopy = '''
      program P;
      type
        TR = record
          Names: array[0..1] of string;
        end;
      procedure Run();
      var
        R1: TR;
        R2: TR;
      begin
        R1.Names[0] := 'x';
        R2 := R1;
      end;
      begin
        Run();
      end.
      ''';

  SrcSAElemFree = '''
      program P;
      type
        TC = class
        public
          X: Integer;
        end;
      procedure Run();
      var
        A: array[0..1] of TC;
      begin
        A[0] := TC.Create();
        A[0].Free();
      end;
      begin
        Run();
      end.
      ''';

procedure TARCTests.TestARC_StaticArrayElemFree_NilsSlot;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemFree);
  { The Free lowering must nil the ELEMENT slot (a computed temp address) —
    `storel 0, %_tN`.  Variable nil-inits go to %_var_* slots and the array
    itself is memset, so a zero store through a temp only appears when the
    element-receiver Free arm is present. }
  AssertTrue('A[0].Free() nils the element slot (storel 0 through a temp)',
    IRContains(IR, 'storel 0, %_t'));
end;

procedure TARCTests.TestARC_StaticArrayElem_OwnedClassRhs_NoRetain;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemOwnedClass);
  AssertEquals('only MakeC''s Result-assign retains; the element store ' +
    'consumes the transferred +1',
    1, CountSubstring(IR, 'call $_ClassAddRef'));
end;

procedure TARCTests.TestARC_StaticArrayElem_BorrowedClassRhs_Retains;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemBorrowedClass);
  AssertEquals('constructor-assign + element store both retain',
    2, CountSubstring(IR, 'call $_ClassAddRef'));
end;

procedure TARCTests.TestARC_StaticArrayElem_OwnedStringRhs_NoRetain;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemOwnedString);
  AssertEquals('only MakeS''s Result-assign retains; the element store ' +
    'consumes the transferred +1',
    1, CountSubstring(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StaticArrayElem_BorrowedStringRhs_Retains;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemBorrowedString);
  AssertEquals('B-assign + element store both retain',
    2, CountSubstring(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_DynArrayElem_OwnedClassRhs_NoRetain;
var
  IR: string;
begin
  IR := GenIR(SrcDynElemOwnedClass);
  AssertEquals('only MakeC''s Result-assign retains; the dyn element store ' +
    'consumes the transferred +1',
    1, CountSubstring(IR, 'call $_ClassAddRef'));
end;

procedure TARCTests.TestARC_DynArrayElem_BorrowedClassRhs_Retains;
var
  IR: string;
begin
  IR := GenIR(SrcDynElemBorrowedClass);
  AssertEquals('constructor-assign + dyn element store both retain',
    2, CountSubstring(IR, 'call $_ClassAddRef'));
end;

procedure TARCTests.TestARC_FieldElemStore_OwnedStringRhs_NoRetain;
var
  IR: string;
begin
  IR := GenIR(SrcFieldElemOwnedString);
  AssertEquals('only MakeS''s Result-assign retains; the field-array ' +
    'element store consumes the transferred +1',
    1, CountSubstring(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_StaticArrayOfClass_BlockExitRelease;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemBorrowedClass);
  { element-store old-value release + B's scope-exit release + the two
    element slots released by the BUG-016 stage-2 scope-exit walk. }
  AssertEquals('both elements released at block exit',
    4, CountSubstring(IR, 'call $_ClassRelease'));
end;

procedure TARCTests.TestARC_StaticArrayOfString_BlockExitRelease;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemBorrowedString);
  { B-assign old + element-store old + B scope-exit + 2 element slots. }
  AssertEquals('both string elements released at block exit',
    5, CountSubstring(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StaticArrayOfRecord_BlockExitRelease;
var
  IR: string;
begin
  IR := GenIR(SrcSAOfRecord);
  { R.S-assign old + record-copy old + R scope-exit + 2 element records'
    S fields via the array -> record -> string recursion. }
  AssertEquals('array->record->string recursion releases both elements',
    5, CountSubstring(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_StaticArrayBlockExitRelease_DoesNotZeroSlots;
var
  IR: string;
begin
  IR := GenIR(SrcSAElemBorrowedClass);
  { Pins the AZero split: the NORMAL-path scope-exit walk passes
    AZero=False, so the only zero store is B's nil-init.  (The exception-
    path walk — EmitExcPathArcCleanup, currently unreferenced since
    4fc5d2c5 — passes AZero=True for idempotency under nested handlers.) }
  AssertEquals('normal-path element release does not zero the slots',
    1, CountSubstring(IR, 'storel 0,'));
end;

procedure TARCTests.TestARC_RecordWithStaticArrayField_ReleaseFields;
var
  IR: string;
begin
  IR := GenIR(SrcRecArrayField);
  { element-store old + R's scope-exit field walk descending into the
    2-element Names array. }
  AssertEquals('record field walk releases the static-array elements',
    3, CountSubstring(IR, 'call $_StringRelease'));
end;

procedure TARCTests.TestARC_RecordWithStaticArrayField_AddRefFields;
var
  IR: string;
begin
  IR := GenIR(SrcRecArrayFieldByValParam);
  { element-store retain in Run + Show's value-param entry retain of both
    Names elements. }
  AssertEquals('value-param entry retains the static-array elements',
    3, CountSubstring(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_RecordCopy_StaticArrayField_RetainsElements;
var
  IR: string;
begin
  IR := GenIR(SrcRecArrayFieldCopy);
  { element-store retain + the R2 := R1 record copy retaining both Names
    elements of the source. }
  AssertEquals('record copy retains the static-array elements',
    3, CountSubstring(IR, 'call $_StringAddRef'));
end;

procedure TARCTests.TestARC_RecordReturn_StaticArrayOnly_IsSret;
var
  IR: string;
begin
  { A record whose ONLY managed content is a static-array field must be
    classified as managed and returned via sret.  RecretManagedClean lacked
    a tyStaticArray case, so a 16-byte record of two strings was "clean" and
    REGISTER-returned — bypassing the ARC copy discipline entirely
    (BUG-20260721-recretclean-static-array-of-managed). }
  IR := GenIR(
    '''
      program P;
      type
        TR = record
          Names: array[0..1] of string;
        end;
      function Make(): TR;
      begin
        Result.Names[0] := 'x';
      end;
      var
        R: TR;
      begin
        R := Make();
      end.
      ''');
  AssertTrue('static-array-of-string record returns via sret',
    IRContains(IR, 'function $Make(l %_par__sret)'));
end;

initialization
  RegisterTest(TARCTests);

end.
