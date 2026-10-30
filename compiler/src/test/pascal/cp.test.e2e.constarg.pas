{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.constarg;

{ E2E parity tests for const-string argument ARC and call-argument
  materialisation, run on BOTH backends (QBE and native).

  Two bug families pinned here:

  1. Const-string caller protection (native port of the QBE shape-aware
     convention): every call path — direct, method, interface dispatch,
     proc-pointer, method-pointer, >6-arg, inherited, interface-sret —
     must keep an rc=0 concat transient or +1 owned return alive across
     the call and free it exactly once afterwards.

  2. Record-returning calls as arguments: the native backend interleaved
     the callee's sret buffer between pushed argument slots, so the pop
     loop read buffer words instead of arguments (garbage values).  The
     fix hoists record-call arguments into the pre-call region.

  3. Indirect calls (proc ptr / method ptr) loaded the target pointer
     into %r10/%r11 BEFORE evaluating arguments; an argument containing
     a call clobbered them (caller-saved), so the callq jumped wild. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EConstArgTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_RecordCallArg_Direct;
    procedure TestRun_RecordCallArg_SevenArgs;
    procedure TestRun_RecordCallArg_Method;
    procedure TestRun_RecordCallArg_ManagedField;
    procedure TestRun_ProcPtrArg_ContainsCall;
    procedure TestRun_MethodPtrArg_ContainsCall;
    procedure TestRun_ConstStr_ConcatDirect;
    procedure TestRun_ConstStr_ConcatMethod;
    procedure TestRun_ConstStr_ConcatInterface;
    procedure TestRun_ConstStr_OwnedReturn;
    procedure TestRun_ConstStr_SeventhSlot;
    procedure TestRun_ConstStr_ProcPtr;
    procedure TestRun_ConstStr_MethodPtr;
    procedure TestRun_ConstStr_GlobalReassignedByCallee;
    procedure TestRun_ConstStr_VarSiblingAlias;
    procedure TestRun_ConstStr_IntfSretArgs;
    procedure TestRun_ConstStr_Inherited;
    procedure TestRun_ConstStr_BorrowedLocalStillUsable;
    procedure TestRun_ConstStr_ConcatOfOwnedReturns;
    procedure TestRun_OutStrForward_SevenSlotMethod;
    procedure TestRun_CharCoerce_SubscriptCompare;
  end;

implementation

procedure TE2EConstArgTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-constarg');
end;

const
  LE = #10;

  SrcRecArgDirect = '''
      program P;
      type
        TR = record
          A, B, C: Int64;
        end;
      function MkRec(): TR;
      begin
        Result.A := 11;
        Result.B := 22;
        Result.C := 33;
      end;
      function UseRec(R: TR; X: Int): Int64;
      begin
        Result := R.A + R.C + X;
      end;
      begin
        WriteLn(UseRec(MkRec(), 5));
      end.
      ''';

  SrcRecArgSeven = '''
      program P;
      type
        TR = record
          A, B, C: Int64;
        end;
      function MkRec(): TR;
      begin
        Result.A := 100;
        Result.B := 200;
        Result.C := 300;
      end;
      function Use7(A, B, C, D, E, F: Int; R: TR): Int64;
      begin
        Result := A + B + C + D + E + F + R.B;
      end;
      begin
        WriteLn(Use7(1, 2, 3, 4, 5, 6, MkRec()));
      end.
      ''';

  SrcRecArgMethod = '''
      program P;
      type
        TR = record
          A, B: Int64;
        end;
        TUser = class
        public
          function Take(R: TR): Int64;
        end;
      function TUser.Take(R: TR): Int64;
      begin
        Result := R.A * R.B;
      end;
      function MkRec(): TR;
      begin
        Result.A := 6;
        Result.B := 7;
      end;
      var U: TUser;
      begin
        U := TUser.Create();
        WriteLn(U.Take(MkRec()));
      end.
      ''';

  SrcRecArgManaged = '''
      program P;
      type
        TR = record
          Name: string;
          N: Int64;
        end;
      function MkRec(): TR;
      begin
        Result.Name := 'rec' + IntToStr(7);
        Result.N := 9;
      end;
      function UseRec(R: TR): string;
      begin
        Result := R.Name + '/' + IntToStr(R.N);
      end;
      begin
        WriteLn(UseRec(MkRec()));
      end.
      ''';

  SrcProcPtrArgCall = '''
      program P;
      type
        TFn = procedure(X: Int);
      procedure Show(X: Int);
      begin
        WriteLn(X);
      end;
      function Bump(X: Int): Int;
      begin
        Result := X + 1;
      end;
      var F: TFn;
      begin
        F := @Show;
        F(Bump(3));
      end.
      ''';

  SrcMethodPtrArgCall = '''
      program P;
      type
        TMeth = procedure(X: Int) of object;
        TObj = class
        public
          procedure Show(X: Int);
        end;
      procedure TObj.Show(X: Int);
      begin
        WriteLn(X);
      end;
      function Bump(X: Int): Int;
      begin
        Result := X + 1;
      end;
      var
        O: TObj;
        M: TMeth;
      begin
        O := TObj.Create();
        M := @O.Show;
        M(Bump(41));
      end.
      ''';

  SrcConcatDirect = '''
      program P;
      procedure Show(const S: string);
      begin
        WriteLn(S);
      end;
      var L: string;
      begin
        L := IntToStr(42);
        Show('v=' + L);
      end.
      ''';

  SrcConcatMethod = '''
      program P;
      type
        TPrinter = class
        public
          procedure Show(const S: string);
        end;
      procedure TPrinter.Show(const S: string);
      begin
        WriteLn(S);
      end;
      var
        Pr: TPrinter;
        L: string;
      begin
        Pr := TPrinter.Create();
        L := IntToStr(7);
        Pr.Show('m=' + L);
      end.
      ''';

  SrcConcatInterface = '''
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
        WriteLn(S);
      end;
      var
        O: TSink;
        I: ISink;
        L: string;
      begin
        O := TSink.Create();
        I := O;
        L := IntToStr(3);
        I.Put('i=' + L);
      end.
      ''';

  SrcOwnedReturn = '''
      program P;
      procedure Show(const S: string);
      begin
        WriteLn(S);
      end;
      function Mk(): string;
      begin
        Result := 'mk' + IntToStr(5);
      end;
      begin
        Show(Mk());
      end.
      ''';

  SrcSeventhSlot = '''
      program P;
      procedure Show7(A, B, C, D, E, F: Int; const S: string);
      begin
        WriteLn(A + B + C + D + E + F);
        WriteLn(S);
      end;
      var L: string;
      begin
        L := IntToStr(99);
        Show7(1, 2, 3, 4, 5, 6, 's=' + L);
      end.
      ''';

  SrcProcPtrConstStr = '''
      program P;
      type
        TFn = procedure(const S: string);
      procedure Show(const S: string);
      begin
        WriteLn(S);
      end;
      var
        F: TFn;
        L: string;
      begin
        F := @Show;
        L := IntToStr(8);
        F('p=' + L);
      end.
      ''';

  SrcMethodPtrConstStr = '''
      program P;
      type
        TMeth = procedure(const S: string) of object;
        TObj = class
        public
          procedure Show(const S: string);
        end;
      procedure TObj.Show(const S: string);
      begin
        WriteLn(S);
      end;
      var
        O: TObj;
        M: TMeth;
        L: string;
      begin
        O := TObj.Create();
        M := @O.Show;
        L := IntToStr(4);
        M('o=' + L);
      end.
      ''';

  SrcGlobalReassign = '''
      program P;
      var G: string;
      procedure Show(const S: string);
      begin
        G := 'changed';
        WriteLn(S);
      end;
      begin
        G := 'orig' + IntToStr(1);
        Show(G);
        WriteLn(G);
      end.
      ''';

  SrcVarSibling = '''
      program P;
      procedure Swapish(const A: string; var B: string);
      begin
        B := 'new';
        WriteLn(A);
      end;
      var L: string;
      begin
        L := 'old' + IntToStr(2);
        Swapish(L, L);
        WriteLn(L);
      end.
      ''';

  SrcIntfSretArgs = '''
      program P;
      type
        IThing = interface
          procedure Touch;
        end;
        TThing = class(TObject, IThing)
        public
          FTag: string;
          procedure Touch;
        end;
      procedure TThing.Touch;
      begin
        WriteLn(FTag);
      end;
      function Wrap(const S: string): IThing;
      var
        T: TThing;
      begin
        T := TThing.Create();
        T.FTag := S + '!';
        Result := T;
      end;
      var
        V: IThing;
        L: string;
      begin
        L := IntToStr(6);
        V := Wrap('w=' + L);
        V.Touch();
      end.
      ''';

  SrcInherited = '''
      program P;
      type
        TBase = class
        public
          procedure Show(const S: string); virtual;
        end;
        TChild = class(TBase)
        public
          procedure Show(const S: string); override;
        end;
      procedure TBase.Show(const S: string);
      begin
        WriteLn('base:' + S);
      end;
      procedure TChild.Show(const S: string);
      begin
        inherited Show(S + '+kid');
      end;
      var
        C: TChild;
        L: string;
      begin
        C := TChild.Create();
        L := IntToStr(5);
        C.Show('c=' + L);
      end.
      ''';

  SrcBorrowedUsable = '''
      program P;
      procedure Sink(const S: string);
      begin
        WriteLn(S);
      end;
      function Mk(): string;
      begin
        Result := 'live' + IntToStr(3);
      end;
      var L: string;
      begin
        L := Mk();
        Sink(L);
        WriteLn(L);
      end.
      ''';

  SrcConcatOwned = '''
      program P;
      procedure Show(const S: string);
      begin
        WriteLn(S);
      end;
      function MkA(): string;
      begin
        Result := 'a' + IntToStr(1);
      end;
      function MkB(): string;
      begin
        Result := 'b' + IntToStr(2);
      end;
      begin
        Show(MkA() + MkB());
      end.
      ''';

  SrcOutStrForward7 = '''
      program P;
      type
        TWorker = class
        public
          procedure Fill(A, B, C, D, E: Int; out S: string);
          procedure Run(out S: string);
        end;
      procedure TWorker.Fill(A, B, C, D, E: Int; out S: string);
      begin
        S := 'sum=' + IntToStr(A + B + C + D + E);
      end;
      procedure TWorker.Run(out S: string);
      begin
        Self.Fill(1, 2, 3, 4, 5, S);
      end;
      var
        W: TWorker;
        R: string;
      begin
        W := TWorker.Create();
        W.Run(R);
        WriteLn(R);
      end.
      ''';

  SrcCharCoerce = '''
      program P;
      var
        S: string;
        I, N: Int;
      begin
        S := 'a,b,c';
        N := 0;
        for I := 0 to Length(S) - 1 do
          if S[I] = ',' then
            N := N + 1;
        WriteLn(N);
      end.
      ''';

procedure TE2EConstArgTests.TestRun_RecordCallArg_Direct;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecArgDirect, '49' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_RecordCallArg_SevenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecArgSeven, '221' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_RecordCallArg_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecArgMethod, '42' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_RecordCallArg_ManagedField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecArgManaged, 'rec7/9' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ProcPtrArg_ContainsCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcPtrArgCall, '4' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_MethodPtrArg_ContainsCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrArgCall, '42' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_ConcatDirect;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConcatDirect, 'v=42' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_ConcatMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConcatMethod, 'm=7' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_ConcatInterface;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConcatInterface, 'i=3' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_OwnedReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOwnedReturn, 'mk5' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_SeventhSlot;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSeventhSlot, '21' + LE + 's=99' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_ProcPtr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcPtrConstStr, 'p=8' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_MethodPtr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrConstStr, 'o=4' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_GlobalReassignedByCallee;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { S must survive the callee's reassignment of G (pin keeps the old buffer
    alive until the call returns). }
  AssertRunsOnAll(SrcGlobalReassign, 'orig1' + LE + 'changed' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_VarSiblingAlias;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A aliases L which the callee rewrites through B — A must still read the
    old buffer during the call. }
  AssertRunsOnAll(SrcVarSibling, 'old2' + LE + 'new' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_IntfSretArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfSretArgs, 'w=6!' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_Inherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInherited, 'base:c=5+kid' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_BorrowedLocalStillUsable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBorrowedUsable, 'live3' + LE + 'live3' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_ConstStr_ConcatOfOwnedReturns;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConcatOwned, 'a1b2' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_OutStrForward_SevenSlotMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { An out-string param forwarded into a >6-slot method call: the native
    >6 inline blocks passed the slot's ADDRESS instead of the held pointer
    (no ParamMode check), so the callee wrote the result into the caller's
    param slot rather than through it. }
  AssertRunsOnAll(SrcOutStrForward7, 'sum=15' + LE, 0);
end;

procedure TE2EConstArgTests.TestRun_CharCoerce_SubscriptCompare;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { S[I] = ',' — the native backend emitted the literal's data POINTER
    instead of honouring IsCharCoerce, so the byte never matched. }
  AssertRunsOnAll(SrcCharCoerce, '2' + LE, 0);
end;

initialization
  RegisterTest(TE2EConstArgTests);

end.
