{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.atomics;

{ E2E tests for the runtime.atomic pointer-width primitives that back the
  migration-safe allocator's remote-free queue
  (docs/concurrent-allocator-design.adoc, §"The new atomic primitives"):
  _AtomicCASPtr, _AtomicXchgPtr, _AtomicAddInt64.

  The primitives live in the RTL (runtime.atomic.pas, inline-asm bodies built
  by the native backend), so a program compiled with EITHER backend links them
  from the RTL objects.  The test programs bind them via `external name` —
  the QBE backend cannot compile an asm-bodied unit pulled in via `uses`, but
  it links the RTL-provided symbols fine — and assert on stdout, which pins
  the Boolean/pointer return ABI across both backends. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EAtomicsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { _AtomicCASPtr: success installs and returns True; failure leaves the
      word untouched and returns False.  Exercised in a condition so a
      garbage-upper-bits Boolean return is caught. }
    procedure TestRun_AtomicCASPtr_SuccessAndFailure;

    { _AtomicXchgPtr: returns the previous value and installs the new one. }
    procedure TestRun_AtomicXchgPtr_ReturnsPrevious;

    { _AtomicAddInt64: fetch-add returns the PREVIOUS value; deltas and
      values wider than 32 bits prove the 64-bit operation. }
    procedure TestRun_AtomicAddInt64_FetchAdd;

    { Treiber-stack push/drain round trip: CAS-push three nodes, XCHG-drain,
      walk the claimed list — the exact protocol RemoteFreePush and
      DrainRemoteFrees use. }
    procedure TestRun_AtomicTreiberPushDrain;
  end;

implementation

procedure TE2EAtomicsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-atomics');
end;

procedure TE2EAtomicsTests.TestRun_AtomicCASPtr_SuccessAndFailure;
const Src = '''
    program T;
    function _AtomicCASPtr(Ptr: Pointer; Expected, NewVal: Pointer): Boolean;
      external name '_AtomicCASPtr';
    var
      Slot: Pointer;
      A, B, C: Int;
    begin
      Slot := @A;
      if _AtomicCASPtr(@Slot, @A, @B) then
        WriteLn('cas1 ok')
      else
        WriteLn('cas1 FAIL');
      if Slot = Pointer(@B) then
        WriteLn('installed')
      else
        WriteLn('not installed');
      if _AtomicCASPtr(@Slot, @C, @A) then
        WriteLn('cas2 FAIL')
      else
        WriteLn('cas2 rejected');
      if Slot = Pointer(@B) then
        WriteLn('unchanged')
      else
        WriteLn('clobbered')
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    'cas1 ok' + Chr(10) + 'installed' + Chr(10)
    + 'cas2 rejected' + Chr(10) + 'unchanged' + Chr(10), 0);
end;

procedure TE2EAtomicsTests.TestRun_AtomicXchgPtr_ReturnsPrevious;
const Src = '''
    program T;
    function _AtomicXchgPtr(Ptr: Pointer; NewVal: Pointer): Pointer;
      external name '_AtomicXchgPtr';
    var
      Slot: Pointer;
      A, B: Int;
      Old: Pointer;
    begin
      Slot := @A;
      Old := _AtomicXchgPtr(@Slot, @B);
      if Old = Pointer(@A) then
        WriteLn('old ok')
      else
        WriteLn('old FAIL');
      if Slot = Pointer(@B) then
        WriteLn('new ok')
      else
        WriteLn('new FAIL');
      Old := _AtomicXchgPtr(@Slot, nil);
      if Old = Pointer(@B) then
        WriteLn('drain ok')
      else
        WriteLn('drain FAIL');
      if Slot = nil then
        WriteLn('nil ok')
      else
        WriteLn('nil FAIL')
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    'old ok' + Chr(10) + 'new ok' + Chr(10)
    + 'drain ok' + Chr(10) + 'nil ok' + Chr(10), 0);
end;

procedure TE2EAtomicsTests.TestRun_AtomicAddInt64_FetchAdd;
const Src = '''
    program T;
    function _AtomicAddInt64(Ptr: Pointer; Delta: Int64): Int64;
      external name '_AtomicAddInt64';
    var
      V: Int64;
      Old: Int64;
    begin
      V := 10;
      Old := _AtomicAddInt64(@V, 32);
      WriteLn(Old);
      WriteLn(V);
      { 64-bit width proof: value and delta both exceed 32 bits }
      V := 4294967296;
      Old := _AtomicAddInt64(@V, 8589934596);
      WriteLn(Old);
      WriteLn(V);
      Old := _AtomicAddInt64(@V, -12884901892);
      WriteLn(V)
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '10' + Chr(10) + '42' + Chr(10)
    + '4294967296' + Chr(10) + '12884901892' + Chr(10) + '0' + Chr(10), 0);
end;

procedure TE2EAtomicsTests.TestRun_AtomicTreiberPushDrain;
const Src = '''
    program T;
    type
      PNode = ^TNode;
      TNode = record
        Next: PNode;
        Tag: Int;
      end;
    function _AtomicCASPtr(Ptr: Pointer; Expected, NewVal: Pointer): Boolean;
      external name '_AtomicCASPtr';
    function _AtomicXchgPtr(Ptr: Pointer; NewVal: Pointer): Pointer;
      external name '_AtomicXchgPtr';
    var
      Head: Pointer;
      N1, N2, N3: TNode;
      Claimed: PNode;
      Sum: Int;
    procedure Push(N: PNode);
    var
      OldHead: Pointer;
    begin
      repeat
        OldHead := Head;
        N^.Next := PNode(OldHead);
      until _AtomicCASPtr(@Head, OldHead, Pointer(N));
    end;
    begin
      Head := nil;
      N1.Tag := 1;
      N2.Tag := 20;
      N3.Tag := 300;
      Push(@N1);
      Push(@N2);
      Push(@N3);
      Claimed := PNode(_AtomicXchgPtr(@Head, nil));
      if Head = nil then
        WriteLn('head drained');
      Sum := 0;
      while Claimed <> nil do
      begin
        Sum := Sum + Claimed^.Tag;
        Claimed := Claimed^.Next;
      end;
      WriteLn(Sum)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'head drained' + Chr(10) + '321' + Chr(10), 0);
end;

initialization
  RegisterTest(TE2EAtomicsTests);

end.
