{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - the analysis engine (application service at the centre of the
  hexagon).

  It orchestrates the pipeline and depends only on abstractions: a source
  provider (where the files come from), the config (how rules behave), and the
  rule registry (what to check).  For each file it builds one TSourceModel and
  runs every enabled rule against it, collecting findings into a shared report.

  A file that fails to parse still runs the line/token rules; the parse failure
  itself surfaces as a BL-0000 diagnostic (suppressible via config). }

unit Guard.Engine;

interface

uses
  SysUtils,
  Generics.Collections,
  Guard.Domain,
  Guard.Report,
  Guard.Config,
  Guard.Frontend,
  Guard.Sources,
  Guard.Rules;

const
  RULE_PARSE_ERROR = 'BL-0000';

type
  TAnalysisEngine = class
  private
    [Unretained] FConfig: TGuardConfig;   { borrowed - owned by the caller }
    FFrontend: TFrontend;
    procedure RunRulesOn(AModel: TSourceModel; AReport: TReport);
    procedure AnalyseModel(AModel: TSourceModel; AReport: TReport);
  public
    constructor Create(AConfig: TGuardConfig);

    { Analyse one file into AReport.  Returns True when the file parsed. }
    function AnalyseFile(const APath: string; AReport: TReport): Boolean;

    { Analyse in-memory source text; returns a fresh, sorted report.  The
      primary seam for tests - no filesystem involved. }
    function AnalyseSourceText(const AName, ASource: string): TReport;

    { Analyse every file a provider yields.  Returns a fresh, sorted report. }
    function Run(AProvider: ISourceProvider): TReport;
  end;

implementation

constructor TAnalysisEngine.Create(AConfig: TGuardConfig);
begin
  inherited Create();
  FConfig   := AConfig;
  FFrontend := TFrontend.Create();
end;

procedure TAnalysisEngine.RunRulesOn(AModel: TSourceModel; AReport: TReport);
var
  I:    Integer;
  Rule: IRule;
  Ctx:  TRuleContext;
  Sev:  TSeverity;
begin
  for I := 0 to RegisteredRuleCount - 1 do
  begin
    Rule := RegisteredRule(I);
    if not FConfig.IsEnabled(Rule.Id) then
      Continue;
    Sev := FConfig.EffectiveSeverity(Rule.Id, Rule.DefaultSeverity);
    Ctx := TRuleContext.Create(Rule.Id, AModel,
                               FConfig.RuleConfig(Rule.Id), AReport, Sev);
    Rule.Analyse(Ctx);
  end;
end;

procedure TAnalysisEngine.AnalyseModel(AModel: TSourceModel; AReport: TReport);
begin
  if (not AModel.ParseOk) and FConfig.IsEnabled(RULE_PARSE_ERROR) then
    AReport.Add(TDiagnostic.Create(RULE_PARSE_ERROR,
      'Parse error: ' + AModel.ParseError,
      FConfig.EffectiveSeverity(RULE_PARSE_ERROR, sevWarning),
      SourceLoc(AModel.FileName, 1, 1)));
  RunRulesOn(AModel, AReport);
end;

function TAnalysisEngine.AnalyseFile(const APath: string; AReport: TReport): Boolean;
var
  Model: TSourceModel;
begin
  try
    Model := FFrontend.Load(APath);
  except
    on E: Exception do
    begin
      AReport.Add(TDiagnostic.Create(RULE_PARSE_ERROR,
        'Could not read source: ' + E.Message, sevError,
        SourceLoc(APath, 1, 1)));
      Exit(False);
    end;
  end;

  AnalyseModel(Model, AReport);
  Result := Model.ParseOk;
end;

function TAnalysisEngine.AnalyseSourceText(const AName, ASource: string): TReport;
var
  Model: TSourceModel;
begin
  Result := TReport.Create();
  Model  := FFrontend.LoadSource(AName, ASource);
  AnalyseModel(Model, Result);
  Result.SortForOutput();
end;

function TAnalysisEngine.Run(AProvider: ISourceProvider): TReport;
var
  Files: TList<string>;
  I:     Integer;
begin
  Result := TReport.Create();
  Files  := AProvider.Collect();
  for I := 0 to Files.Count - 1 do
    AnalyseFile(Files[I], Result);
  Result.SortForOutput();
end;

end.
