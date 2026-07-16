{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - the analysis report: an ordered collection of diagnostics plus
  the summary statistics every formatter and the CI exit-code logic need.

  TReport is the aggregate root the engine hands to a formatter.  It owns its
  diagnostics through ARC (they live in a TList<TDiagnostic>); dropping the
  report releases them. }

unit Guard.Report;

interface

uses
  SysUtils,
  Generics.Collections,
  Guard.Domain;

type
  TReport = class
  private
    FItems: TList<TDiagnostic>;
    function GetCount: Integer;
    function GetItem(AIndex: Integer): TDiagnostic;
  public
    constructor Create;

    { Append a finding.  The report takes shared ownership via ARC. }
    procedure Add(ADiag: TDiagnostic);

    { Number of diagnostics at exactly the given severity. }
    function CountOf(ASeverity: TSeverity): Integer;

    { The most severe level present, or sevInfo when the report is empty.
      AHasAny reports whether any diagnostic exists at all. }
    function HighestSeverity(out AHasAny: Boolean): TSeverity;

    { True when at least one diagnostic is >= AThreshold - the predicate the
      --fail-on CLI switch turns into a non-zero exit code. }
    function HasAtLeast(AThreshold: TSeverity): Boolean;

    { Stable order for deterministic output: by file, then line, then column,
      then rule id.  Formatters call this before emitting. }
    procedure SortForOutput;

    property Count: Integer read GetCount;
    property Items[AIndex: Integer]: TDiagnostic read GetItem; default;
  end;

implementation

constructor TReport.Create;
begin
  inherited Create();
  FItems := TList<TDiagnostic>.Create();
end;

procedure TReport.Add(ADiag: TDiagnostic);
begin
  FItems.Add(ADiag);
end;

function TReport.GetCount: Integer;
begin
  Result := FItems.Count;
end;

function TReport.GetItem(AIndex: Integer): TDiagnostic;
begin
  Result := FItems[AIndex];
end;

function TReport.CountOf(ASeverity: TSeverity): Integer;
var
  D: TDiagnostic;
begin
  Result := 0;
  for D in FItems do
    if D.Severity = ASeverity then
      Inc(Result);
end;

function TReport.HighestSeverity(out AHasAny: Boolean): TSeverity;
var
  D: TDiagnostic;
begin
  AHasAny := FItems.Count > 0;
  Result  := sevInfo;
  for D in FItems do
    if Ord(D.Severity) > Ord(Result) then
      Result := D.Severity;
end;

function TReport.HasAtLeast(AThreshold: TSeverity): Boolean;
var
  D: TDiagnostic;
begin
  Result := False;
  for D in FItems do
    if Ord(D.Severity) >= Ord(AThreshold) then
      Exit(True);
end;

function DiagLess(const A, B: TDiagnostic): Boolean;
begin
  if A.Location.FileName <> B.Location.FileName then
    Exit(A.Location.FileName < B.Location.FileName);
  if A.Location.Line <> B.Location.Line then
    Exit(A.Location.Line < B.Location.Line);
  if A.Location.Col <> B.Location.Col then
    Exit(A.Location.Col < B.Location.Col);
  Result := A.RuleId < B.RuleId;
end;

procedure TReport.SortForOutput;
var
  I, J: Integer;
  Tmp:  TDiagnostic;
begin
  { Insertion sort - report sizes are small, and it keeps the comparison
    logic in one obvious place without needing a comparator closure. }
  for I := 1 to FItems.Count - 1 do
  begin
    J := I;
    while (J > 0) and DiagLess(FItems[J], FItems[J - 1]) do
    begin
      Tmp := FItems[J];
      FItems[J] := FItems[J - 1];
      FItems[J - 1] := Tmp;
      Dec(J);
    end;
  end;
end;

end.
