{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.afterconstruction;

{ TObject.AfterConstruction: a virtual method the compiler calls once on a
  new instance after its outermost constructor returns -- not after an
  inherited Create inside the chain -- as Delphi and FPC do.  TThread
  starts its OS thread there, so a subclass constructor has finished before
  Execute runs.

  Lowering, pinned here on both ISAs:
  - TFoo.Create(...): the runtime class is TFoo, so the override is known
    statically and called directly; a class that does not override it gets
    no call at all (TObject's is empty);
  - construction through a class reference (C.Create(), ClassCreate) calls
    vtable slot 2, offset 24 -- the third TObject built-in after Destroy
    and ToString.
  cp.test.e2e.afterconstruction runs the programs. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.harness;

type
  TAfterConstructionTests = class(TTestCase)
  published
    procedure TestOverride_Accepted;
    procedure TestInherited_FromDirectTObjectChild_Accepted;
    procedure TestInherited_ThroughClassNotDeclaringIt_Accepted;
    procedure TestVTable_HasAfterConstructionSlot;
    procedure TestStaticCreate_CallsOverrideDirectly;
    procedure TestStaticCreate_NoArgs_CallsOverrideDirectly;
    procedure TestStaticCreate_NoOverride_NoCall;
    procedure TestMetaclassCreate_DispatchesThroughVTable;
  end;

implementation

const
  SrcOverride =
    'program p;'#10 +
    'type'#10 +
    '  TFoo = class'#10 +
    '    constructor Create(N: Int32);'#10 +
    '    procedure AfterConstruction; override;'#10 +
    '  end;'#10 +
    'constructor TFoo.Create(N: Int32);'#10 +
    'begin'#10 +
    'end;'#10 +
    'procedure TFoo.AfterConstruction;'#10 +
    'begin'#10 +
    '  inherited AfterConstruction();'#10 +
    '  WriteLn(''after'');'#10 +
    'end;'#10 +
    'var F: TFoo;'#10 +
    'begin'#10 +
    '  F := TFoo.Create(1);'#10 +
    'end.'#10;

  { the call sequence a class-reference construction emits (x86-64 pads
    the stack around the indirect call, so its pattern stops at the load) }
  X86VSlot = 'movq (%rdi), %rax'#10#9'movq 24(%rax), %rax';
  Arm64VSlot = 'ldr x9, [x0]'#10#9'ldr x9, [x9, #24]'#10#9'blr x9';

procedure TAfterConstructionTests.TestOverride_Accepted;
begin
  AssertEquals('', SemanticError(SrcOverride));
end;

procedure TAfterConstructionTests.TestInherited_FromDirectTObjectChild_Accepted;
begin
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'type'#10 +
    '  TFoo = class(TObject)'#10 +
    '    procedure AfterConstruction; override;'#10 +
    '  end;'#10 +
    'procedure TFoo.AfterConstruction;'#10 +
    'begin'#10 +
    '  inherited AfterConstruction();'#10 +
    'end;'#10 +
    'begin'#10 +
    'end.'#10));
end;

procedure TAfterConstructionTests.TestInherited_ThroughClassNotDeclaringIt_Accepted;
begin
  { TMid declares no AfterConstruction: TLeaf's inherited call reaches
    TObject's }
  AssertEquals('', SemanticError(
    'program p;'#10 +
    'type'#10 +
    '  TMid = class'#10 +
    '  end;'#10 +
    '  TLeaf = class(TMid)'#10 +
    '    procedure AfterConstruction; override;'#10 +
    '  end;'#10 +
    'procedure TLeaf.AfterConstruction;'#10 +
    'begin'#10 +
    '  inherited AfterConstruction();'#10 +
    'end;'#10 +
    'begin'#10 +
    'end.'#10));
end;

procedure TAfterConstructionTests.TestVTable_HasAfterConstructionSlot;
begin
  { the root vtable: typeinfo, Destroy, ToString, AfterConstruction }
  AssertEquals('', AsmMissing(
    'program p;'#10 +
    'type TFoo = class end;'#10 +
    'var F: TFoo;'#10 +
    'begin'#10 +
    '  F := TFoo.Create();'#10 +
    'end.'#10,
    '.quad TObject_ToString'#10#9'.quad TObject_AfterConstruction',
    '.quad _TObject_ToString'#10#9'.quad _TObject_AfterConstruction'));
end;

procedure TAfterConstructionTests.TestStaticCreate_CallsOverrideDirectly;
begin
  AssertEquals('', AsmMissing(SrcOverride, 'callq TFoo_AfterConstruction',
    'bl _TFoo_AfterConstruction'));
end;

procedure TAfterConstructionTests.TestStaticCreate_NoArgs_CallsOverrideDirectly;
begin
  AssertEquals('', AsmMissing(
    'program p;'#10 +
    'type'#10 +
    '  TFoo = class'#10 +
    '    procedure AfterConstruction; override;'#10 +
    '  end;'#10 +
    'procedure TFoo.AfterConstruction;'#10 +
    'begin'#10 +
    'end;'#10 +
    'var F: TFoo;'#10 +
    'begin'#10 +
    '  F := TFoo.Create();'#10 +
    '  F := TFoo.Create;'#10 +
    'end.'#10,
    'callq TFoo_AfterConstruction', 'bl _TFoo_AfterConstruction'));
end;

procedure TAfterConstructionTests.TestStaticCreate_NoOverride_NoCall;
var
  Src: string;
begin
  Src :=
    'program p;'#10 +
    'type TFoo = class end;'#10 +
    'var F: TFoo;'#10 +
    'begin'#10 +
    '  F := TFoo.Create();'#10 +
    'end.'#10;
  AssertTrue('x86-64: no call',
    Pos('callq TObject_AfterConstruction', GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('x86-64: no dispatch', Pos(X86VSlot, GenAsm(Src, TargetX86_64)) < 0);
  AssertTrue('arm64: no call',
    Pos('bl _TObject_AfterConstruction', GenAsm(Src, TargetArm64)) < 0);
  AssertTrue('arm64: no dispatch', Pos(Arm64VSlot, GenAsm(Src, TargetArm64)) < 0);
end;

procedure TAfterConstructionTests.TestMetaclassCreate_DispatchesThroughVTable;
begin
  AssertEquals('', AsmMissing(
    'program p;'#10 +
    'type'#10 +
    '  TBase = class'#10 +
    '    constructor Create; virtual;'#10 +
    '  end;'#10 +
    '  TBaseClass = class of TBase;'#10 +
    'constructor TBase.Create;'#10 +
    'begin'#10 +
    'end;'#10 +
    'var C: TBaseClass; B: TBase;'#10 +
    'begin'#10 +
    '  C := TBase;'#10 +
    '  B := C.Create();'#10 +
    'end.'#10,
    X86VSlot, Arm64VSlot));
end;

initialization
  RegisterTest(TAfterConstructionTests);

end.
