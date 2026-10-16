{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.recordret;

{ Return-ABI coverage for records returned by value.

  Between two Blaise routines the caller and callee always agree on how a
  record comes back, so a wrong classification is invisible when the
  program runs (cp.test.e2e.recordret round-trips every class); it only
  shows at the C boundary.  These tests pin the platform ABI on both ISAs,
  which classify differently: SysV x86-64 splits an Integer + Double record
  across %rax and %xmm0, while AAPCS64 returns a mixed record in x0:x1 and
  only a homogeneous floating-point aggregate in d registers.  A managed
  field or a record over 16 bytes goes through the hidden result pointer
  (%rdi / x8) on both. }

interface

uses
  blaise.testing, cp.test.harness;

type
  TRecordReturnTests = class(TTestCase)
  private
    function Callee(const ASrc, AName, ATarget: string): string;
  published
    { TC.SGetI(); -- a discarded static method's interface result still needs
      a buffer for the callee to write: both ISAs called it with none }
    procedure TestCodegen_DiscardedStaticIntfResult_PassesBuffer;
    { GetB()(5).S: a record result through the procedural value an expression
      yields gets a result buffer -- x8 on arm64 (which refused the form), the
      hidden first argument on x86-64 (which passed none and crashed) }
    procedure TestCodegen_ExprCalleeRecordResult_PassesBuffer;
    { a hoisted interface-call result passed to a record-returning call fills
      BOTH slots of its argument (the slot path reloaded one) }
    procedure TestCodegen_SretCall_IntfResultArg_BothHalves;
    { record-returning calls on x86-64 use the shared slot path: an open
      array argument (rejected), and a VIRTUAL method past the registers
      (dispatched statically, its var argument passed by value) }
    procedure TestCodegen_SretCall_OpenArrayArg_Lowered;
    procedure TestCodegen_SretMethodOverflow_DispatchesVirtually;
    procedure TestReturnAbi_TwoInt64_IntegerRegisterPair;
    procedure TestReturnAbi_OneDouble_FloatRegister;
    procedure TestReturnAbi_TwoDoubles_FloatRegisterPair;
    procedure TestReturnAbi_IntegerPlusDouble_PerIsaClassification;
    procedure TestReturnAbi_ManagedField_HiddenResultPointer;
    procedure TestReturnAbi_Over16Bytes_HiddenResultPointer;
    { A discarded record-returning call on an interface FIELD of Self
      (FS.MakeRect(5); inside a method) must dispatch through the field, not
      through a global FS_obj/FS_itab pair that does not exist (x86-64). }
    procedure TestDiscardedIntfRecordCall_ImplicitSelfField_UsesTheField;
    { a record returned through a closure / procedural variable: assigned,
      read, passed on and discarded -- a 16-byte one in registers, a 24-byte
      one through the hidden result pointer }
    procedure TestCodegen_ClosureRecordReturn_RegisterShape;
    procedure TestCodegen_ClosureRecordReturn_SretShape;
    { a DISCARDED result through a procedural value needs its own buffer: x8
      held whatever was left in it, and the callee wrote through it }
    procedure TestCodegen_DiscardedSretThroughProcValue_HasBuffer;
    { a record returned by a C routine is lowered on both ISAs (arm64 refused
      it as unvalidated) }
    procedure TestCodegen_ExternalRecordReturn_Lowers;
    { a discarded string result of a method on a named receiver is released }
    procedure TestCodegen_DiscardedStringOnNamedReceiver_Released;
    { a float method called on implicit Self, used where a float is wanted }
    procedure TestCodegen_ImplicitSelfFloatCall_InFloatContext;
    { ... and a VIRTUAL one dispatches through the vtable: x86-64 called the
      declaring class's body, so an override never ran }
    procedure TestCodegen_ImplicitSelfFloatCall_Virtual_DispatchesThroughVtable;
  end;

implementation

const
  ClosureRecSrc = '''
    program P;
    type
      TSmall = record A, B: Int64; end;
      TBig = record A, B, C: Int64; end;
      TFnS = reference to function(X: Integer): TSmall;
      TFnB = reference to function(X: Integer): TBig;
    procedure ShowS(const R: TSmall); begin WriteLn(R.A + R.B) end;
    procedure ShowB(const R: TBig); begin WriteLn(R.A + R.C) end;
    var GS: TFnS; GB: TFnB; S: TSmall; B: TBig;
    begin
      GS := function(X: Integer): TSmall
        begin Result.A := X; Result.B := X + 1 end;
      GB := function(X: Integer): TBig
        begin Result.A := X; Result.B := 2; Result.C := X + 3 end;
      S := GS(1);
      WriteLn(GS(2).B);
      ShowS(GS(3));
      GS(4);
      B := GB(5);
      WriteLn(GB(6).C);
      ShowB(GB(7));
      GB(8)
    end.
    ''';

function TRecordReturnTests.Callee(const ASrc, AName, ATarget: string): string;
var
  AsmText, Lbl: string;
  P, E: Integer;
begin
  { The callee's body, from its label to its first ret.  The programs below
    have an empty main, so the patterns cannot come from a caller. }
  AsmText := GenAsm(ASrc, ATarget);
  if ATarget = TargetArm64 then
    Lbl := #10 + '_' + AName + ':'
  else
    Lbl := #10 + AName + ':';
  P := Pos(Lbl, AsmText);
  AssertTrue(ATarget + ': ' + AName + ' emitted', P >= 0);
  Result := Copy(AsmText, P, Length(AsmText) - P);
  E := Pos(#9 + 'ret', Result);
  AssertTrue(ATarget + ': ' + AName + ' returns', E >= 0);
  Result := Copy(Result, 0, E);
end;

procedure TRecordReturnTests.TestReturnAbi_TwoInt64_IntegerRegisterPair;
const
  Src = '''
    program P;
    type T2L = record A, B: Int64; end;
    function MakeL: T2L; begin Result.A := 11; Result.B := 22 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: second eightbyte in %rdx',
    Pos('movq 8(%rcx), %rdx', Callee(Src, 'MakeL', TargetX86_64)) >= 0);
  AssertTrue('arm64: second eightbyte in x1',
    Pos('ldr x1, [x9, #8]', Callee(Src, 'MakeL', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_OneDouble_FloatRegister;
const
  Src = '''
    program P;
    type T1D = record X: Double; end;
    function MakeD: T1D; begin Result.X := 1.5 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: returned in %xmm0',
    Pos('%xmm0', Callee(Src, 'MakeD', TargetX86_64)) >= 0);
  AssertTrue('arm64: returned in d0',
    Pos('ldr d0, ', Callee(Src, 'MakeD', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_TwoDoubles_FloatRegisterPair;
const
  Src = '''
    program P;
    type T2D = record X, Y: Double; end;
    function MakeD: T2D; begin Result.X := 1.5; Result.Y := 2.5 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: second double in %xmm1',
    Pos('movsd 8(%rcx), %xmm1', Callee(Src, 'MakeD', TargetX86_64)) >= 0);
  AssertTrue('arm64: homogeneous float aggregate in d0:d1',
    Pos('ldr d1, [x9, #8]', Callee(Src, 'MakeD', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_IntegerPlusDouble_PerIsaClassification;
const
  Src = '''
    program P;
    type TID = record I: Integer; D: Double; end;
    function MakeID: TID; begin Result.I := 3; Result.D := 4.5 end;
    begin end.
    ''';
var
  X86, A64: string;
begin
  X86 := Callee(Src, 'MakeID', TargetX86_64);
  AssertTrue('x86-64: INTEGER eightbyte in %rax',
    Pos('movq (%rcx), %rax', X86) >= 0);
  AssertTrue('x86-64: SSE eightbyte in %xmm0',
    Pos('movsd 8(%rcx), %xmm0', X86) >= 0);
  A64 := Callee(Src, 'MakeID', TargetArm64);
  AssertTrue('arm64: a mixed record is not an HFA -- second half in x1',
    Pos('ldr x1, [x9, #8]', A64) >= 0);
  AssertTrue('arm64: no d-register return for a mixed record',
    (Pos('ldr d0, [x9, #0]', A64) < 0) and (Pos('ldr d1, [x9, #8]', A64) < 0));
end;

procedure TRecordReturnTests.TestReturnAbi_ManagedField_HiddenResultPointer;
const
  Src = '''
    program P;
    type TS = record S: string; end;
    function MakeS: TS; begin Result.S := 'x' end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: the result pointer arrives in %rdi',
    Pos('movq %rdi, ', Callee(Src, 'MakeS', TargetX86_64)) >= 0);
  AssertTrue('arm64: the result pointer arrives in x8',
    Pos('stur x8, ', Callee(Src, 'MakeS', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestReturnAbi_Over16Bytes_HiddenResultPointer;
const
  Src = '''
    program P;
    type T3 = record A, B, C: Int64; end;
    function Make3: T3; begin Result.A := 1; Result.C := 3 end;
    begin end.
    ''';
begin
  AssertTrue('x86-64: the result pointer arrives in %rdi',
    Pos('movq %rdi, ', Callee(Src, 'Make3', TargetX86_64)) >= 0);
  AssertTrue('arm64: the result pointer arrives in x8',
    Pos('stur x8, ', Callee(Src, 'Make3', TargetArm64)) >= 0);
end;

procedure TRecordReturnTests.TestDiscardedIntfRecordCall_ImplicitSelfField_UsesTheField;
const
  Src = '''
    program P;
    type
      TRect = record Name: string; N: Integer; end;
      IShape = interface
        function MakeRect(AN: Integer): TRect;
      end;
      TUser = class
        FS: IShape;
        procedure Go();
      end;
    procedure TUser.Go();
    begin
      FS.MakeRect(5)
    end;
    begin
    end.
    ''';
var
  AsmT: string;
begin
  AsmT := GenAsm(Src, TargetX86_64);
  AssertTrue('x86-64: no global FS_obj receiver', Pos('FS_obj', AsmT) < 0);
  AssertTrue('x86-64: no global FS_itab receiver', Pos('FS_itab', AsmT) < 0);
  AssertTrue('x86-64: dispatched through the itab', Pos(#9'callq *%r11', AsmT) >= 0);
end;

const
  SrcSretShapes = '''
    program P;
    type
      TBig = record A, B, C: Int64; end;
      TBase = class
        function Calc(A, B, C, D, E: Integer; var Z: Integer): TBig; virtual;
      end;
    function TBase.Calc(A, B, C, D, E: Integer; var Z: Integer): TBig;
    begin Result.A := A + E; Z := 1 end;
    function OA(const V: array of Integer; K: Integer): TBig;
    begin Result.A := High(V); Result.C := K end;
    var O: TBase; R: TBig; Z: Integer;
    begin
      O := TBase.Create();
      R := O.Calc(1, 2, 3, 4, 5, Z);
      R := OA([1, 2, 3], 7);
      WriteLn(R.A, Z)
    end.
    ''';

procedure TRecordReturnTests.TestCodegen_SretCall_OpenArrayArg_Lowered;
begin
  AssertEquals('OA lowers', '',
    AsmMissing(SrcSretShapes, #9'callq OA'#10, #9'bl _OA'#10));
end;

procedure TRecordReturnTests.TestCodegen_SretMethodOverflow_DispatchesVirtually;
const
  Src = '''
    program P;
    type
      TBig = record A, B, C: Int64; end;
      TBase = class
        function Calc(A, B, C, D, E: Integer; var Z: Integer): TBig; virtual;
      end;
    function TBase.Calc(A, B, C, D, E: Integer; var Z: Integer): TBig;
    begin Result.A := A + E; Z := 1 end;
    var O: TBase; R: TBig; Z: Integer;
    begin
      O := TBase.Create();
      R := O.Calc(1, 2, 3, 4, 5, Z);
      WriteLn(R.A, Z)
    end.
    ''';
begin
  AssertEquals('Calc goes through the vtable', '',
    AsmMissing(Src,
      #9'movq (%rsi), %rax'#10#9'movq 24(%rax), %rax'#10#9'callq *%rax',
      #9'blr '));
end;

procedure TRecordReturnTests.TestCodegen_SretCall_IntfResultArg_BothHalves;
const
  Src = '''
    program P;
    type
      IS1 = interface function V: Integer; end;
      TS = class(TObject, IS1) N: Integer; function V: Integer; end;
      TBig = record A, B, C: Int64; end;
    function TS.V: Integer; begin Result := N end;
    function MkS(K: Integer): IS1; var T: TS; begin T := TS.Create(); T.N := K; Result := T end;
    function SR(const I: IS1; K: Integer): TBig; begin Result.A := I.V(); Result.B := K end;
    var R: TBig;
    begin
      R := SR(MkS(9), 8);
      WriteLn(R.A)
    end.
    ''';
begin
  AssertEquals('obj and itab both copied into the slot block', '',
    AsmMissing(Src,
      #9'movq 32(%rsp), %rax'#10#9'movq %rax, 8(%rsp)'#10 +
        #9'movq 40(%rsp), %rax'#10#9'movq %rax, 16(%rsp)',
      #9'bl _SR'#10));
end;

procedure TRecordReturnTests.TestCodegen_ClosureRecordReturn_RegisterShape;
begin
  { x86-64 calls through the closure's code word (callq *); arm64 blr's it.
    Neither used to lower the call at all (arm64: 'record address of this
    expression'). }
  AssertEquals('closure record return lowers', '',
    AsmMissing(ClosureRecSrc, 'callq *', 'blr x'));
end;

procedure TRecordReturnTests.TestCodegen_ClosureRecordReturn_SretShape;
var
  A: string;
begin
  { the 24-byte result comes back through the hidden result pointer: arm64
    points x8 at the destination before the indirect call }
  A := GenAsm(ClosureRecSrc, TargetArm64);
  AssertTrue('arm64 passes a result buffer in x8', Pos(#9'sub x8, x29, #', A) >= 0);
  { x86-64: the hidden result pointer takes %rdi, so the closure environment
    moves to %rsi -- the convention a record-returning method uses }
  A := GenAsm(ClosureRecSrc, TargetX86_64);
  AssertTrue('x86-64 passes the environment in %rsi behind the result pointer',
    Pos(#9'movq 8(%r11), %rsi', A) >= 0);
end;

procedure TRecordReturnTests.TestCodegen_DiscardedSretThroughProcValue_HasBuffer;
var
  A: string;
begin
  A := GenAsm('''
    program P;
    type
      TBig = record A, B, C: Int64; end;
      TM = function: TBig of object;
      TH = class function Mk: TBig; end;
    function TH.Mk: TBig; begin Result.A := 1 end;
    var H: TH; M: TM;
    begin H := TH.Create(); M := @H.Mk; M() end.
    ''', TargetArm64);
  AssertTrue('the call sets x8 to a result buffer', Pos(#9'sub x8, x29, #', A) >= 0);
end;

procedure TRecordReturnTests.TestCodegen_ExternalRecordReturn_Lowers;
begin
  AssertEquals('external record return lowers', '',
    AsmMissing('''
      program P;
      type TDiv = record Quot, Rem: Integer; end;
      function c_div(N, D: Integer): TDiv; external name 'div';
      var A: TDiv;
      begin A := c_div(17, 5); WriteLn(A.Quot) end.
      ''', 'call', 'bl _div'));
end;

procedure TRecordReturnTests.TestCodegen_DiscardedStringOnNamedReceiver_Released;
const
  Src = '''
    program P;
    type TC = class function Mk: string; end;
    function TC.Mk: string; begin Result := Copy('abc', 0, 2) end;
    var C: TC;
    begin C := TC.Create(); C.Mk() end.
    ''';
var
  A: string;
  P: Integer;
begin
  { the release must follow the call in the main body -- the callee's own
    code releases strings too, so the whole listing proves nothing }
  A := GenAsm(Src, TargetX86_64);
  P := Pos(#10'main:', A);
  AssertTrue('x86-64 main releases the discarded string',
    (P >= 0) and (PosEx('callq _StringRelease', A, P) >= 0));
  A := GenAsm(Src, TargetArm64);
  P := Pos(#10'_main:', A);
  AssertTrue('arm64 main releases the discarded string',
    (P >= 0) and (PosEx('bl __StringRelease', A, P) >= 0));
end;

procedure TRecordReturnTests.TestCodegen_ImplicitSelfFloatCall_InFloatContext;
begin
  { Trunc(Half(9.0)) inside a method: the implicit-Self call is evaluated as a
    float operand.  arm64 reported 'this call form in float context'. }
  AssertEquals('implicit-Self float call lowers', '',
    AsmMissing('''
      program P;
      type
        TC = class
          function Half(X: Double): Double;
          procedure Go;
        end;
      function TC.Half(X: Double): Double; begin Result := X / 2.0 end;
      procedure TC.Go; var I: Integer; begin I := Trunc(Half(9.0)); WriteLn(I) end;
      var C: TC;
      begin C := TC.Create(); C.Go() end.
      ''', 'call', 'fcvtzs'));
end;

procedure TRecordReturnTests.TestCodegen_ImplicitSelfFloatCall_Virtual_DispatchesThroughVtable;
begin
  AssertEquals('virtual implicit-Self float call goes through the vtable', '',
    AsmMissing('''
      program P;
      type
        TBase = class
          function Half(X: Double): Double; virtual;
          procedure Go;
        end;
      function TBase.Half(X: Double): Double; begin Result := X / 2.0 end;
      procedure TBase.Go; var D: Double; begin D := Half(5.0) + 1.0; WriteLn(D:0:1) end;
      var B: TBase;
      begin B := TBase.Create(); B.Go() end.
      ''', 'callq *', 'blr x'));
end;

procedure TRecordReturnTests.TestCodegen_ExprCalleeRecordResult_PassesBuffer;
const
  Src = '''
    program P;
    type
      TBig = record A, B, C: Int64; S: string; end;
      TBFn = reference to function(A: Integer): TBig;
    function GetB(): TBFn;
    begin
      Result := function(A: Integer): TBig begin Result.S := 'B'; end;
    end;
    begin
      WriteLn(GetB()(5).S)
    end.
    ''';
var
  A: string;
  P: Integer;
begin
  AssertEquals('the indirect call takes a result pointer', '',
    AsmMissing(Src, #9'movq 16(%rsp), %rdi'#10#9'callq *%r10',
      #9'ldr x9, [x10]'#10#9'blr x9'));
  A := GenAsm(Src, TargetArm64);
  P := Pos(#9'ldr x9, [x10]'#10#9'blr x9', A);
  AssertTrue('arm64: x8 points at the buffer just before the call',
    Pos(#9'sub x8, x29, #', Copy(A, P - 60, 60)) >= 0);
end;

procedure TRecordReturnTests.TestCodegen_DiscardedStaticIntfResult_PassesBuffer;
const
  Src = '''
    program P;
    type
      IThing = interface function Name(): string; end;
      TC = class(TObject, IThing)
        function Name(): string;
        static function SGetI(): IThing;
      end;
    function TC.Name(): string; begin Result := 'n' end;
    static function TC.SGetI(): IThing; begin Result := TC.Create() end;
    begin
      TC.SGetI()
    end.
    ''';
begin
  AssertEquals('the call is given a result buffer', '',
    AsmMissing(Src, #9'movq %rsp, %rdi'#10#9'callq TC_SGetI',
      #9'sub x8, x29, #'));
  AssertTrue('arm64: x8 is set right before the call',
    Pos(#10#9'bl _TC_SGetI', GenAsm(Src, TargetArm64)) >
    Pos(#9'sub x8, x29, #', GenAsm(Src, TargetArm64)));
end;

initialization
  RegisterTest(TRecordReturnTests);

end.
