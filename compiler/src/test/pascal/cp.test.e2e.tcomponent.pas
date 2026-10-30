{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tcomponent;

{ E2E tests for TComponent from the RTL Classes unit.
  Covers: Create(nil), Create(AOwner), Name property, Owner property,
  Components[] access, ComponentCount, automatic child destruction. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ETComponentTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_CreateNilOwner;
    procedure TestRun_Name;
    procedure TestRun_OwnerRef;
    procedure TestRun_ComponentCount;
    procedure TestRun_ComponentsArray;
    procedure TestRun_OwnerFreesChildren;
  end;

implementation

const
  SrcCreateNilOwner =
    '''
    program P;
    uses Classes;
    var C: TComponent;
    begin
      C := TComponent.Create(nil);
      WriteLn(C.Owner = nil);
      WriteLn(C.ComponentCount);
      C.Free()
    end.
    ''';

  SrcName =
    '''
    program P;
    uses Classes;
    var C: TComponent;
    begin
      C := TComponent.Create(nil);
      C.Name := 'MyComp';
      WriteLn(C.Name);
      C.Free()
    end.
    ''';

  SrcOwnerRef =
    '''
    program P;
    uses Classes;
    var Parent, Child: TComponent;
    begin
      Parent := TComponent.Create(nil);
      Child  := TComponent.Create(Parent);
      WriteLn(Child.Owner = Parent);
      Parent.Free()
    end.
    ''';

  SrcComponentCount =
    '''
    program P;
    uses Classes;
    var Parent, C1, C2, C3: TComponent;
    begin
      Parent := TComponent.Create(nil);
      C1 := TComponent.Create(Parent);
      C2 := TComponent.Create(Parent);
      C3 := TComponent.Create(Parent);
      WriteLn(Parent.ComponentCount);
      Parent.Free()
    end.
    ''';

  SrcComponentsArray =
    '''
    program P;
    uses Classes;
    var Parent, C1, C2: TComponent;
    begin
      Parent := TComponent.Create(nil);
      C1 := TComponent.Create(Parent);
      C1.Name := 'first';
      C2 := TComponent.Create(Parent);
      C2.Name := 'second';
      WriteLn(Parent.Components[0].Name);
      WriteLn(Parent.Components[1].Name);
      Parent.Free()
    end.
    ''';

  SrcOwnerFreesChildren =
    '''
    program P;
    uses Classes;
    var Parent, C1, C2: TComponent;
    begin
      Parent := TComponent.Create(nil);
      C1 := TComponent.Create(Parent);
      C2 := TComponent.Create(Parent);
      WriteLn(Parent.ComponentCount);
      Parent.Free();
      { If we reach here without crash, children were freed cleanly }
      WriteLn('ok')
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ETComponentTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tcomponent')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ETComponentTests.TestRun_CreateNilOwner;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCreateNilOwner, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Owner=nil is true',     'True', Lines.Strings[0]);
    AssertEquals('ComponentCount=0',      '0', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2ETComponentTests.TestRun_Name;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcName, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Name=MyComp', 'MyComp', Trim(Output));
end;

procedure TE2ETComponentTests.TestRun_OwnerRef;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcOwnerRef, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Child.Owner=Parent', 'True', Trim(Output));
end;

procedure TE2ETComponentTests.TestRun_ComponentCount;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcComponentCount, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('ComponentCount=3', '3', Trim(Output));
end;

procedure TE2ETComponentTests.TestRun_ComponentsArray;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcComponentsArray, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Components[0].Name=first',  'first',  Lines.Strings[0]);
    AssertEquals('Components[1].Name=second', 'second', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2ETComponentTests.TestRun_OwnerFreesChildren;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcOwnerFreesChildren, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('ComponentCount=2 before Free', '2',  Lines.Strings[0]);
    AssertEquals('ok after Free',                'ok', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

initialization
  RegisterTest(TE2ETComponentTests);

end.
