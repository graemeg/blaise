{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.attributes;

{ E2E tests for custom attribute RTTI: the attribute tables codegen lays out
  in typeinfo slots 7 (class attributes, as typeinfo/factory-thunk pairs) and
  8 (published-method attributes) are read back at run time by
  HasClassAttribute, GetClassAttribute and the method-attribute builtins.
  Parser and semantic tests live in cp.test.attributes.pas. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EAttributeTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_HasClassAttribute_True;
    procedure TestRun_HasClassAttribute_False;
    procedure TestRun_HasClassAttribute_InheritedFromParent;
    procedure TestRun_HasClassAttribute_MultipleAttributes;
    procedure TestRun_GetClassAttribute_ReifiesConstructorArgs;
    procedure TestRun_GetClassAttribute_AbsentReturnsNil;
    procedure TestRun_MethodAttributes_HasGetCountAt;
  end;

implementation

const
  LE = #10;

procedure TE2EAttributeTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-attributes')
end;

procedure TE2EAttributeTests.TestRun_HasClassAttribute_True;
const
  Src =
    '''
    program P;
    type
      ThreadedAttribute = class(TCustomAttribute) end;
      [Threaded]
      TFoo = class(TObject) end;
    begin
      WriteLn(HasClassAttribute(TFoo, ThreadedAttribute))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_HasClassAttribute_False;
const
  Src =
    '''
    program P;
    type
      ThreadedAttribute = class(TCustomAttribute) end;
      TBar = class(TObject) end;
    begin
      WriteLn(HasClassAttribute(TBar, ThreadedAttribute))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'False' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_HasClassAttribute_InheritedFromParent;
const
  Src =
    '''
    program P;
    type
      ThreadedAttribute = class(TCustomAttribute) end;
      [Threaded]
      TBase = class(TObject) end;
      TChild = class(TBase) end;
    begin
      WriteLn(HasClassAttribute(TBase, ThreadedAttribute));
      WriteLn(HasClassAttribute(TChild, ThreadedAttribute))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_HasClassAttribute_MultipleAttributes;
const
  Src =
    '''
    program P;
    type
      AttrA = class(TCustomAttribute) end;
      AttrB = class(TCustomAttribute) end;
      [AttrA]
      [AttrB]
      TFoo = class(TObject) end;
    begin
      WriteLn(HasClassAttribute(TFoo, AttrA));
      WriteLn(HasClassAttribute(TFoo, AttrB))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True' + LE + 'True' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_GetClassAttribute_ReifiesConstructorArgs;
const
  Src =
    '''
    program P;
    type
      TestCaseAttribute = class(TCustomAttribute)
      private
        FName: string;
        FArgs: string;
      public
        constructor Create(AName, AArgs: string);
        property Name: string read FName;
        property Args: string read FArgs;
      end;
      [TestCase('simple', '2,2,4')]
      TFoo = class(TObject) end;
    constructor TestCaseAttribute.Create(AName, AArgs: string);
    begin
      FName := AName;
      FArgs := AArgs;
    end;
    var
      A:  TObject;
      TC: TestCaseAttribute;
    begin
      A := GetClassAttribute(TFoo, TestCaseAttribute);
      if A = nil then
        WriteLn('nil')
      else
      begin
        TC := TestCaseAttribute(A);
        WriteLn(TC.Name + '|' + TC.Args)
      end
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'simple|2,2,4' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_GetClassAttribute_AbsentReturnsNil;
const
  Src =
    '''
    program P;
    type
      MarkAttribute = class(TCustomAttribute) end;
      TBar = class(TObject) end;
    var
      A: TObject;
    begin
      A := GetClassAttribute(TBar, MarkAttribute);
      if A = nil then
        WriteLn('nil')
      else
        WriteLn('instance')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'nil' + LE, 0);
end;

procedure TE2EAttributeTests.TestRun_MethodAttributes_HasGetCountAt;
const
  Src =
    '''
    program P;
    type
      MarkAttribute = class(TCustomAttribute)
      private
        FTag: string;
      public
        constructor Create(ATag: string);
        property Tag: string read FTag;
      end;
      TFoo = class(TObject)
      published
        [Mark('alpha')]
        [Mark('beta')]
        procedure Run;
      end;
    constructor MarkAttribute.Create(ATag: string);
    begin
      FTag := ATag;
    end;
    procedure TFoo.Run;
    begin
    end;
    var
      A: TObject;
      M: MarkAttribute;
    begin
      WriteLn(MethodAttributeCount(TFoo, 'Run'));
      WriteLn(HasMethodAttribute(TFoo, 'Run', MarkAttribute));
      WriteLn(HasMethodAttribute(TFoo, 'Missing', MarkAttribute));
      A := GetMethodAttributeAt(TFoo, 'Run', 1);
      M := MarkAttribute(A);
      WriteLn(M.Tag);
      A := GetMethodAttribute(TFoo, 'Run', MarkAttribute);
      M := MarkAttribute(A);
      WriteLn(M.Tag)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2' + LE + 'True' + LE + 'False' + LE + 'beta' + LE + 'alpha' + LE, 0);
end;

initialization
  RegisterTest(TE2EAttributeTests);

end.
