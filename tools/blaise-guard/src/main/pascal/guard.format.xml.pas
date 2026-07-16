{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - XML report formatter (machine-readable output).

  Emits, via the stdlib streaming XML writer:

    <?xml version="1.0" encoding="UTF-8"?>
    <blaise-guard>
      <summary total="N" error="X" warning="Y" info="Z"/>
      <diagnostics>
        <diagnostic ruleId="BL-1001" severity="warning"
                    file="..." line="1" col="1" length="5">
          <message>...</message>
          <quickFix title="...">
            <replacement>...</replacement>
          </quickFix>
        </diagnostic>
      </diagnostics>
    </blaise-guard> }

unit Guard.Format.Xml;

interface

uses
  Guard.Report,
  Guard.Format;

type
  TXmlFormatter = class(IReportFormatter)
  public
    function Render(AReport: TReport): string;
  end;

implementation

uses
  SysUtils,
  Xml.Writer,
  Guard.Domain;

function TXmlFormatter.Render(AReport: TReport): string;
var
  W: TXMLWriter;
  I: Integer;
  D: TDiagnostic;
begin
  W := TXMLWriter.Create();
  W.WriteDeclaration();
  W.BeginElement('blaise-guard');

    W.BeginElement('summary');
      W.WriteAttribute('total',   IntToStr(AReport.Count));
      W.WriteAttribute('error',   IntToStr(AReport.CountOf(sevError)));
      W.WriteAttribute('warning', IntToStr(AReport.CountOf(sevWarning)));
      W.WriteAttribute('info',    IntToStr(AReport.CountOf(sevInfo)));
    W.EndElement();

    W.BeginElement('diagnostics');
    for I := 0 to AReport.Count - 1 do
    begin
      D := AReport[I];
      W.BeginElement('diagnostic');
        W.WriteAttribute('ruleId',   D.RuleId);
        W.WriteAttribute('severity', SeverityToStr(D.Severity));
        W.WriteAttribute('file',     D.Location.FileName);
        W.WriteAttribute('line',     IntToStr(D.Location.Line));
        W.WriteAttribute('col',      IntToStr(D.Location.Col));
        W.WriteAttribute('length',   IntToStr(D.Location.Len));
        W.WriteElement('message', D.Message);
        if D.Fix <> nil then
        begin
          W.BeginElement('quickFix');
            W.WriteAttribute('title', D.Fix.Title);
            if D.Fix.HasReplacement then
              W.WriteElement('replacement', D.Fix.Replacement);
          W.EndElement();
        end;
      W.EndElement();
    end;
    W.EndElement();

  W.EndElement();
  Result := W.ToString();
end;

end.
