{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for TGuardConfig: a config file layers its entries OVER the
  built-in defaults, so a rule the file does not mention behaves exactly as it
  would with no config at all - default-on rules stay on, and BL-1004 (off by
  default) stays off. }

unit Guard.Config.Tests;

interface

uses
  blaise.testing;

type
  TGuardConfigTests = class(TTestCase)
  published
    procedure TestUnlistedRuleIsEnabled;
    procedure TestUnlistedDefaultOffRuleStaysOff;
    procedure TestNoRulesBlockKeepsDefaults;
    procedure TestFileCanEnableDefaultOffRule;
    procedure TestListedWithoutEnabledKeepsDefault;
    procedure TestFileConfigDrivesEngine;
  end;

implementation

uses
  SysUtils,
  Classes,
  Guard.Config,
  Guard.Report,
  Guard.Engine,
  Guard.Test.Support;

const
  NL = #10;
  UNUSED_ID = 'BL-1004';

procedure TGuardConfigTests.TestUnlistedRuleIsEnabled;
var
  Cfg: TGuardConfig;
begin
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1001": { "enabled": true } } }');
  AssertTrue('BL-2006 unlisted -> on', Cfg.IsEnabled('BL-2006'));
end;

procedure TGuardConfigTests.TestUnlistedDefaultOffRuleStaysOff;
var
  Cfg: TGuardConfig;
begin
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1001": { "enabled": true } } }');
  AssertFalse('BL-1004 unlisted -> still off', Cfg.IsEnabled(UNUSED_ID));
end;

procedure TGuardConfigTests.TestNoRulesBlockKeepsDefaults;
var
  Cfg: TGuardConfig;
begin
  Cfg := TGuardConfig.LoadFromString('{ }');
  AssertFalse('BL-1004 off', Cfg.IsEnabled(UNUSED_ID));
  AssertTrue('BL-1001 on', Cfg.IsEnabled('BL-1001'));
end;

procedure TGuardConfigTests.TestFileCanEnableDefaultOffRule;
var
  Cfg: TGuardConfig;
begin
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1004": { "enabled": true } } }');
  AssertTrue('BL-1004 turned on', Cfg.IsEnabled(UNUSED_ID));
end;

procedure TGuardConfigTests.TestListedWithoutEnabledKeepsDefault;
var
  Cfg: TGuardConfig;
begin
  { Tuning a param must not silently switch a default-off rule on. }
  Cfg := TGuardConfig.LoadFromString(
    '{ "rules": { "BL-1004": { "params": { "checkParameters": true } } } }');
  AssertFalse('BL-1004 still off', Cfg.IsEnabled(UNUSED_ID));
end;

procedure TGuardConfigTests.TestFileConfigDrivesEngine;
var
  Path, Src: string;
  SL: TStringList;
  Cfg: TGuardConfig;
  Eng: TAnalysisEngine;
  R: TReport;
begin
  { Through a real file and the analysis engine: a config that omits BL-1004
    must not report the unused local, while default-on rules still run. }
  Path := IncludeTrailingPathDelimiter(GetTempDir()) + 'guard-config-test.json';
  SL := TStringList.Create();
  SL.Text := '{ "rules": { "BL-1001": { "enabled": true, "params": '
    + '{ "maxLength": 20 } } } }';
  SL.SaveToFile(Path);
  try
    Cfg := TGuardConfig.LoadFromFile(Path);
  finally
    DeleteFile(Path);
  end;
  Src :=
    'program T;'                    + NL +
    'procedure Foo;'                + NL +
    'var'                           + NL +
    '  y: Integer;'                 + NL +
    'begin'                         + NL +
    '  WriteLn(''a long line here'');' + NL +
    'end;'                          + NL +
    'begin'                         + NL +
    'end.'                          + NL;
  Eng := TAnalysisEngine.Create(Cfg);
  R := Eng.AnalyseSourceText('t.pas', Src);
  AssertEquals('no BL-1004', 0, CountForRule(R, UNUSED_ID));
  AssertEquals('BL-1001 still runs', 1, CountForRule(R, 'BL-1001'));
end;

initialization
  RegisterTest(TGuardConfigTests);

end.
