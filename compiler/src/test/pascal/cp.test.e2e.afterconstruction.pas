{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.afterconstruction;

{ TObject.AfterConstruction runs once, after the outermost constructor has
  returned, for every way of constructing an instance; a raising
  AfterConstruction destroys the instance.  cp.test.afterconstruction pins
  the lowering. }

interface

uses
  SysUtils, Classes, blaise.testing, cp.test.e2e.base;

type
  TE2EAfterConstructionTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ConstructorChain_AfterConstructionOnceAtTheEnd;
    procedure TestRun_EveryConstructionForm_CallsIt;
    procedure TestRun_Raising_DestroysTheInstance;
    procedure TestRun_InheritedChain_RunsEachLevel;
  end;

implementation

const
  LE = #10;

  { three constructor levels, each calling inherited Create first: the
    hook runs once, after the last of them }
  SrcChain =
    '''
    program P;
    type
      TA = class
        constructor Create;
        procedure AfterConstruction; override;
      end;
      TB = class(TA)
        constructor Create;
      end;
      TC = class(TB)
        constructor Create;
      end;
    constructor TA.Create;
    begin
      WriteLn('A.Create')
    end;
    procedure TA.AfterConstruction;
    begin
      WriteLn('AfterConstruction ', Self.ClassName)
    end;
    constructor TB.Create;
    begin
      inherited Create();
      WriteLn('B.Create')
    end;
    constructor TC.Create;
    begin
      inherited Create();
      WriteLn('C.Create')
    end;
    var X: TA;
    begin
      X := TC.Create();
      WriteLn('built');
      X := TA.Create();
      WriteLn('done')
    end.
    ''';

  { with arguments, without parentheses, discarded as a statement, through
    a class-reference variable (the override of a derived class runs), and
    through ClassCreate }
  SrcForms =
    '''
    program P;
    type
      TBase = class
        constructor Create; virtual;
        procedure AfterConstruction; override;
      end;
      TDerived = class(TBase)
        constructor Create; override;
        procedure AfterConstruction; override;
      end;
      TArgs = class
        FN: Int;
        constructor Create(AN: Int);
        procedure AfterConstruction; override;
      end;
      TBaseClass = class of TBase;
    constructor TBase.Create;
    begin
    end;
    procedure TBase.AfterConstruction;
    begin
      WriteLn('base after')
    end;
    constructor TDerived.Create;
    begin
      inherited Create()
    end;
    procedure TDerived.AfterConstruction;
    begin
      WriteLn('derived after')
    end;
    constructor TArgs.Create(AN: Int);
    begin
      Self.FN := AN
    end;
    procedure TArgs.AfterConstruction;
    begin
      WriteLn('args after ', Self.FN)
    end;
    var
      B: TBase;
      A: TArgs;
      C: TBaseClass;
    begin
      A := TArgs.Create(7);
      B := TBase.Create;
      TBase.Create();
      C := TDerived;
      B := C.Create();
      C.Create();
      B := TBase(ClassCreate(C));
      WriteLn('end')
    end.
    ''';

  { an exception from AfterConstruction propagates, and the instance it was
    called on is destroyed -- as when a constructor raises }
  SrcRaising =
    '''
    program P;
    uses SysUtils;
    type
      TFoo = class
        procedure AfterConstruction; override;
        destructor Destroy; override;
      end;
    procedure TFoo.AfterConstruction;
    begin
      raise Exception.Create('refused')
    end;
    destructor TFoo.Destroy;
    begin
      WriteLn('destroyed');
      inherited Destroy()
    end;
    var F: TFoo;
    begin
      try
        F := TFoo.Create();
        WriteLn('not reached')
      except
        on E: Exception do
          WriteLn('caught ', E.Message)
      end;
      WriteLn(F = nil)
    end.
    ''';

  { overrides calling inherited AfterConstruction run outermost-last }
  SrcInheritedChain =
    '''
    program P;
    type
      TA = class
        procedure AfterConstruction; override;
      end;
      TB = class(TA)
      end;
      TC = class(TB)
        procedure AfterConstruction; override;
      end;
    procedure TA.AfterConstruction;
    begin
      inherited AfterConstruction();
      WriteLn('A')
    end;
    procedure TC.AfterConstruction;
    begin
      inherited AfterConstruction();
      WriteLn('C')
    end;
    var X: TA;
    begin
      X := TC.Create()
    end.
    ''';

procedure TE2EAfterConstructionTests.SetUp;
begin
  inherited SetUp();
  Self.SetUpScratch('compiler/target/test-e2e-afterconstruction');
end;

procedure TE2EAfterConstructionTests.TestRun_ConstructorChain_AfterConstructionOnceAtTheEnd;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run: ' + Output, CompileAndRun(SrcChain, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'A.Create' + LE + 'B.Create' + LE + 'C.Create' + LE +
    'AfterConstruction TC' + LE + 'built' + LE +
    'A.Create' + LE + 'AfterConstruction TA' + LE + 'done' + LE, Output)
end;

procedure TE2EAfterConstructionTests.TestRun_EveryConstructionForm_CallsIt;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run: ' + Output, CompileAndRun(SrcForms, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'args after 7' + LE + 'base after' + LE + 'base after' + LE +
    'derived after' + LE + 'derived after' + LE + 'derived after' + LE +
    'end' + LE, Output)
end;

procedure TE2EAfterConstructionTests.TestRun_Raising_DestroysTheInstance;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run: ' + Output, CompileAndRunWithRTL(SrcRaising, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'destroyed' + LE + 'caught refused' + LE + 'True' + LE, Output)
end;

procedure TE2EAfterConstructionTests.TestRun_InheritedChain_RunsEachLevel;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run: ' + Output, CompileAndRun(SrcInheritedChain, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'A' + LE + 'C' + LE, Output)
end;

initialization
  RegisterTest(TE2EAfterConstructionTests);

end.
