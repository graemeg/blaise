{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - console (terminal) report formatter.

  One line per finding, gcc/clang style so editors and CI log scrapers can
  parse it:

    path:line:col: <severity> BL-1001: Line exceeds 120 characters (134)

  followed by a summary line.  ANSI colour is applied when enabled; disable it
  for pipes/CI with a plain-text run. }

unit Guard.Format.Console;

interface

uses
  Guard.Report,
  Guard.Format;

type
  TConsoleFormatter = class(IReportFormatter)
  private
    FUseColor: Boolean;
  public
    constructor Create(AUseColor: Boolean);
    function Render(AReport: TReport): string;
  end;

implementation

uses
  SysUtils,
  Guard.Domain;

const
  NL  = #10;
  ESC = #27;
  C_RESET  = ESC + '[0m';
  C_RED    = ESC + '[31m';
  C_YELLOW = ESC + '[33m';
  C_CYAN   = ESC + '[36m';
  C_BOLD   = ESC + '[1m';
  C_DIM    = ESC + '[2m';

constructor TConsoleFormatter.Create(AUseColor: Boolean);
begin
  inherited Create();
  FUseColor := AUseColor;
end;

function TConsoleFormatter.Render(AReport: TReport): string;
var
  I:      Integer;
  D:      TDiagnostic;
  SevTxt: string;
  SevCol: string;
  Loc:    string;
  Line:   string;
  Buf:    string;
begin
  Buf := '';
  for I := 0 to AReport.Count - 1 do
  begin
    D := AReport[I];

    case D.Severity of
      sevError:   begin SevTxt := 'error';   SevCol := C_RED;    end;
      sevWarning: begin SevTxt := 'warning'; SevCol := C_YELLOW; end;
    else
      SevTxt := 'info'; SevCol := C_CYAN;
    end;

    Loc := D.Location.FileName + ':' +
           IntToStr(D.Location.Line) + ':' + IntToStr(D.Location.Col) + ':';

    if FUseColor then
      Line := C_BOLD + Loc + C_RESET + ' ' +
              SevCol + SevTxt + C_RESET + ' ' +
              C_DIM + D.RuleId + C_RESET + ': ' + D.Message
    else
      Line := Loc + ' ' + SevTxt + ' ' + D.RuleId + ': ' + D.Message;

    Buf := Buf + Line + NL;

    if D.Fix <> nil then
    begin
      Buf := Buf + '    fix: ' + D.Fix.Title + NL;
      if D.Fix.HasReplacement then
        Buf := Buf + '    suggested: ' + D.Fix.Replacement + NL;
    end;
  end;

  { Summary. }
  Buf := Buf + NL +
    IntToStr(AReport.Count) + ' issue(s): ' +
    IntToStr(AReport.CountOf(sevError))   + ' error(s), ' +
    IntToStr(AReport.CountOf(sevWarning)) + ' warning(s), ' +
    IntToStr(AReport.CountOf(sevInfo))    + ' info' + NL;

  Result := Buf;
end;

end.
