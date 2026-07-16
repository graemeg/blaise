{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Unit tests for the BlaiseGuard domain: severity parsing/ordering and the
  TReport aggregate (counts, thresholds, deterministic sort). }

unit Guard.Domain.Tests;

interface

uses
  blaise.testing;

type
  TGuardDomainTests = class(TTestCase)
  published
    procedure TestSeverityRoundTrip;
    procedure TestSeverityOrdering;
    procedure TestReportCounts;
    procedure TestReportThreshold;
    procedure TestReportSort;
  end;

implementation

uses
  Guard.Domain,
  Guard.Report;

procedure TGuardDomainTests.TestSeverityRoundTrip;
var
  S: TSeverity;
begin
  AssertTrue('parse warning', TryParseSeverity('Warning', S));
  AssertTrue('warning value', S = sevWarning);
  AssertEquals('to string', 'error', SeverityToStr(sevError));
  AssertFalse('reject junk', TryParseSeverity('nope', S));
end;

procedure TGuardDomainTests.TestSeverityOrdering;
begin
  { The --fail-on logic relies on Ord ordering. }
  AssertTrue('info < warning', Ord(sevInfo) < Ord(sevWarning));
  AssertTrue('warning < error', Ord(sevWarning) < Ord(sevError));
end;

procedure TGuardDomainTests.TestReportCounts;
var
  R: TReport;
begin
  R := TReport.Create();
  R.Add(TDiagnostic.Create('BL-1', 'a', sevError,   SourceLoc('f.pas', 1, 1)));
  R.Add(TDiagnostic.Create('BL-2', 'b', sevWarning, SourceLoc('f.pas', 2, 1)));
  R.Add(TDiagnostic.Create('BL-3', 'c', sevWarning, SourceLoc('f.pas', 3, 1)));
  AssertEquals('total', 3, R.Count);
  AssertEquals('errors', 1, R.CountOf(sevError));
  AssertEquals('warnings', 2, R.CountOf(sevWarning));
  AssertEquals('info', 0, R.CountOf(sevInfo));
end;

procedure TGuardDomainTests.TestReportThreshold;
var
  R: TReport;
  H: Boolean;
begin
  R := TReport.Create();
  R.Add(TDiagnostic.Create('BL-1', 'a', sevWarning, SourceLoc('f.pas', 1, 1)));
  AssertTrue ('warning meets warning', R.HasAtLeast(sevWarning));
  AssertFalse('warning below error',  R.HasAtLeast(sevError));
  AssertTrue ('highest is warning', R.HighestSeverity(H) = sevWarning);
  AssertTrue ('has any', H);
end;

procedure TGuardDomainTests.TestReportSort;
var
  R: TReport;
begin
  R := TReport.Create();
  { Add out of order; expect (a.pas:1), (b.pas:5), (b.pas:9) after sort. }
  R.Add(TDiagnostic.Create('BL-9', 'x', sevInfo, SourceLoc('b.pas', 9, 1)));
  R.Add(TDiagnostic.Create('BL-1', 'y', sevInfo, SourceLoc('a.pas', 1, 1)));
  R.Add(TDiagnostic.Create('BL-5', 'z', sevInfo, SourceLoc('b.pas', 5, 1)));
  R.SortForOutput();
  AssertEquals('first file',  'a.pas', R[0].Location.FileName);
  AssertEquals('second line', 5, R[1].Location.Line);
  AssertEquals('third line',  9, R[2].Location.Line);
end;

initialization
  RegisterTest(TGuardDomainTests);

end.
