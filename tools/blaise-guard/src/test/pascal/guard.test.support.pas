{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Shared helpers for BlaiseGuard rule tests: run a single rule (in allowlist
  isolation) over in-memory source and inspect the resulting report. }

unit Guard.Test.Support;

interface

uses
  Guard.Domain,
  Guard.Config,
  Guard.Report;

{ A config in allowlist mode with only ARuleId enabled, so a test exercises one
  rule without noise from the others (or the BL-0000 parse-error diagnostic). }
function IsolatedConfig(const ARuleId: string): TGuardConfig;

{ Number of diagnostics carrying the given rule id. }
function CountForRule(AReport: TReport; const ARuleId: string): Integer;

{ The first diagnostic for ARuleId, or nil. }
function FirstForRule(AReport: TReport; const ARuleId: string): TDiagnostic;

implementation

function IsolatedConfig(const ARuleId: string): TGuardConfig;
begin
  Result := TGuardConfig.Create();
  Result.DefaultEnabled := False;
  Result.RuleConfig(ARuleId).Enabled := True;
end;

function CountForRule(AReport: TReport; const ARuleId: string): Integer;
var
  I: Integer;
begin
  Result := 0;
  for I := 0 to AReport.Count - 1 do
    if AReport[I].RuleId = ARuleId then
      Inc(Result);
end;

function FirstForRule(AReport: TReport; const ARuleId: string): TDiagnostic;
var
  I: Integer;
begin
  Result := nil;
  for I := 0 to AReport.Count - 1 do
    if AReport[I].RuleId = ARuleId then
      Exit(AReport[I]);
end;

end.
