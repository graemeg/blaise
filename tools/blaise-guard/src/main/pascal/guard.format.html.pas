{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - self-contained HTML dashboard formatter.

  Produces a single standalone HTML document (inline CSS, no external assets)
  with a summary header and a table of findings, colour-coded by severity.
  Built with a TStringBuilder for efficiency; all dynamic text is escaped. }

unit Guard.Format.Html;

interface

uses
  Guard.Report,
  Guard.Format;

type
  THtmlFormatter = class(IReportFormatter)
  public
    function Render(AReport: TReport): string;
  end;

implementation

uses
  SysUtils,
  StrUtils,
  Guard.Domain;

const
  NL = #10;

{ Minimal HTML-entity escaping.  Byte-wise (like the stdlib JSONEscape) so it
  is UTF-8 safe: only ASCII specials are rewritten, multibyte sequences pass
  through unchanged. }
function HtmlEscape(const S: string): string;
var
  SB: TStringBuilder;
  I, N: Integer;
  B: Byte;
begin
  SB := TStringBuilder.Create();
  N := Length(S);
  I := 0;
  while I < N do
  begin
    B := Byte(S[I]);
    if B = 38 then SB.Append('&amp;')        { & }
    else if B = 60 then SB.Append('&lt;')    { < }
    else if B = 62 then SB.Append('&gt;')    { > }
    else if B = 34 then SB.Append('&quot;')  { " }
    else SB.AppendByte(B);
    I := I + 1;
  end;
  Result := SB.ToString();
end;

function SeverityClass(ASeverity: TSeverity): string;
begin
  case ASeverity of
    sevError:   Result := 'error';
    sevWarning: Result := 'warning';
  else
    Result := 'info';
  end;
end;

function Head(AReport: TReport): string;
begin
  Result :=
    '<!DOCTYPE html>' + NL +
    '<html lang="en"><head><meta charset="utf-8">' + NL +
    '<meta name="viewport" content="width=device-width, initial-scale=1">' + NL +
    '<title>BlaiseGuard Report</title>' + NL +
    '<style>' + NL +
    ':root{color-scheme:light dark}' +
    'body{font:14px/1.5 system-ui,sans-serif;margin:0;background:#0f1115;color:#e6e6e6}' +
    'header{padding:24px 32px;background:#171a21;border-bottom:1px solid #262b36}' +
    'h1{margin:0 0 4px;font-size:20px}' +
    '.sub{color:#9aa4b2;font-size:13px}' +
    '.tiles{display:flex;gap:12px;margin-top:16px;flex-wrap:wrap}' +
    '.tile{background:#1d222c;border:1px solid #2a3140;border-radius:8px;padding:10px 16px;min-width:80px}' +
    '.tile .n{font-size:22px;font-weight:600}' +
    '.tile .l{color:#9aa4b2;font-size:12px;text-transform:uppercase;letter-spacing:.05em}' +
    'main{padding:24px 32px}' +
    'table{border-collapse:collapse;width:100%;font-size:13px}' +
    'th,td{text-align:left;padding:8px 10px;border-bottom:1px solid #262b36;vertical-align:top}' +
    'th{color:#9aa4b2;font-weight:600;text-transform:uppercase;font-size:11px;letter-spacing:.05em}' +
    'code{font-family:ui-monospace,Menlo,monospace}' +
    '.badge{display:inline-block;padding:1px 8px;border-radius:999px;font-size:11px;font-weight:600}' +
    '.error .badge{background:#3a1418;color:#ff8a8a}' +
    '.warning .badge{background:#3a2e14;color:#ffd479}' +
    '.info .badge{background:#14293a;color:#79c0ff}' +
    '.rule{color:#9aa4b2;font-size:12px}' +
    '.fix{color:#7ee787;font-size:12px;margin-top:4px}' +
    '.empty{padding:40px;text-align:center;color:#9aa4b2}' +
    '</style></head><body>' + NL;
end;

function THtmlFormatter.Render(AReport: TReport): string;
var
  SB: TStringBuilder;
  I:  Integer;
  D:  TDiagnostic;
  Cls: string;
begin
  SB := TStringBuilder.Create();
  SB.Append(Head(AReport));

  SB.Append('<header><h1>BlaiseGuard Report</h1>');
  SB.Append('<div class="sub">Static analysis for the Blaise language</div>');
  SB.Append('<div class="tiles">');
  SB.Append('<div class="tile"><div class="n">' + IntToStr(AReport.Count) +
            '</div><div class="l">Total</div></div>');
  SB.Append('<div class="tile error"><div class="n">' +
            IntToStr(AReport.CountOf(sevError)) + '</div><div class="l">Errors</div></div>');
  SB.Append('<div class="tile warning"><div class="n">' +
            IntToStr(AReport.CountOf(sevWarning)) + '</div><div class="l">Warnings</div></div>');
  SB.Append('<div class="tile info"><div class="n">' +
            IntToStr(AReport.CountOf(sevInfo)) + '</div><div class="l">Info</div></div>');
  SB.Append('</div></header>' + NL);

  SB.Append('<main>');
  if AReport.Count = 0 then
    SB.Append('<div class="empty">No issues found.</div>')
  else
  begin
    SB.Append('<table><thead><tr>' +
      '<th>Severity</th><th>Location</th><th>Rule</th><th>Message</th>' +
      '</tr></thead><tbody>' + NL);
    for I := 0 to AReport.Count - 1 do
    begin
      D   := AReport[I];
      Cls := SeverityClass(D.Severity);
      SB.Append('<tr class="' + Cls + '">');
      SB.Append('<td><span class="badge">' + SeverityToStr(D.Severity) + '</span></td>');
      SB.Append('<td><code>' + HtmlEscape(D.Location.FileName) + ':' +
                IntToStr(D.Location.Line) + ':' + IntToStr(D.Location.Col) +
                '</code></td>');
      SB.Append('<td class="rule">' + HtmlEscape(D.RuleId) + '</td>');
      SB.Append('<td>' + HtmlEscape(D.Message));
      if D.Fix <> nil then
      begin
        SB.Append('<div class="fix">fix: ' + HtmlEscape(D.Fix.Title));
        if D.Fix.HasReplacement then
          SB.Append(' &rarr; <code>' + HtmlEscape(D.Fix.Replacement) + '</code>');
        SB.Append('</div>');
      end;
      SB.Append('</td></tr>' + NL);
    end;
    SB.Append('</tbody></table>' + NL);
  end;
  SB.Append('</main></body></html>' + NL);

  Result := SB.ToString();
end;

end.
