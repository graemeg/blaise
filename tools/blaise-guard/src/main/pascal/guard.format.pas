{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - the report output port (Strategy pattern).

  IReportFormatter is the outbound port every renderer implements: console,
  JSON, XML, HTML.  The CLI's --format switch selects one; the engine and
  report know nothing about presentation. }

unit Guard.Format;

interface

uses
  Guard.Report;

type
  IReportFormatter = interface
    { Render a full report to a single string ready to print or write. }
    function Render(AReport: TReport): string;
  end;

implementation

end.
