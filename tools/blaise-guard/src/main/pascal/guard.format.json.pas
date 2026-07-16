{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - JSON report formatter (machine-readable output).

  Emits a stable document via the stdlib streaming JSON writer:

    { "tool": "blaise-guard",
      "summary": { "total": N, "error": X, "warning": Y, "info": Z },
      "diagnostics": [
        { "ruleId": "BL-1001", "severity": "warning",
          "file": "...", "line": 1, "col": 1, "length": 5,
          "message": "...",
          "quickFix": { "title": "...", "replacement": "..." } }
      ] } }

  quickFix is omitted when a diagnostic has no suggestion. }

unit Guard.Format.Json;

interface

uses
  Guard.Report,
  Guard.Format;

type
  TJsonFormatter = class(IReportFormatter)
  public
    function Render(AReport: TReport): string;
  end;

implementation

uses
  Json.Writer,
  Guard.Domain;

function TJsonFormatter.Render(AReport: TReport): string;
var
  W: TJSONWriter;
  I: Integer;
  D: TDiagnostic;
begin
  W := TJSONWriter.Create();
  W.BeginObject();
    W.WriteString('tool', 'blaise-guard');

    W.WriteKey('summary');
    W.BeginObject();
      W.WriteInt('total',   AReport.Count);
      W.WriteInt('error',   AReport.CountOf(sevError));
      W.WriteInt('warning', AReport.CountOf(sevWarning));
      W.WriteInt('info',    AReport.CountOf(sevInfo));
    W.EndObject();

    W.WriteKey('diagnostics');
    W.BeginArray();
    for I := 0 to AReport.Count - 1 do
    begin
      D := AReport[I];
      W.BeginObject();
        W.WriteString('ruleId',   D.RuleId);
        W.WriteString('severity', SeverityToStr(D.Severity));
        W.WriteString('file',     D.Location.FileName);
        W.WriteInt('line',        D.Location.Line);
        W.WriteInt('col',         D.Location.Col);
        W.WriteInt('length',      D.Location.Len);
        W.WriteString('message',  D.Message);
        if D.Fix <> nil then
        begin
          W.WriteKey('quickFix');
          W.BeginObject();
            W.WriteString('title', D.Fix.Title);
            if D.Fix.HasReplacement then
              W.WriteString('replacement', D.Fix.Replacement);
          W.EndObject();
        end;
      W.EndObject();
    end;
    W.EndArray();
  W.EndObject();

  Result := W.ToString();
end;

end.
