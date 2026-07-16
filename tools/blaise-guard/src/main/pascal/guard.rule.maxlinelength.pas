{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-1001: MaxLineLength.

  Flags source lines longer than a configurable limit (default 120).  A pure
  line rule - it needs neither tokens nor an AST, so it runs even on files the
  parser rejects.

  Config: rules."BL-1001".params.maxLength (Integer). }

unit Guard.Rule.MaxLineLength;

interface

implementation

uses
  SysUtils,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID      = 'BL-1001';
  RULE_NAME    = 'MaxLineLength';
  DEFAULT_MAX  = 120;

type
  TMaxLineLengthRule = class(TLineRuleBase)
  protected
    procedure CheckLine(AContext: TRuleContext; const ALine: string;
                        ALineNo: Integer); override;
  public
    constructor Create;
  end;

constructor TMaxLineLengthRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
end;

procedure TMaxLineLengthRule.CheckLine(AContext: TRuleContext;
  const ALine: string; ALineNo: Integer);
var
  MaxLen: Integer;
  Len:    Integer;
begin
  MaxLen := AContext.RuleCfg.GetInt('maxLength', DEFAULT_MAX);
  Len    := Length(ALine);
  if Len > MaxLen then
    AContext.Emit(
      'Line exceeds ' + IntToStr(MaxLen) + ' characters (' + IntToStr(Len) + ')',
      SourceLoc(AContext.Model.FileName, ALineNo, MaxLen + 1, Len - MaxLen));
end;

initialization
  RegisterRule(TMaxLineLengthRule.Create());

end.
