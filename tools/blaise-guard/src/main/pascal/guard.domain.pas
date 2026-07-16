{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - core domain model.

  This unit is the heart of the hexagon: it depends on nothing but the RTL and
  is free of any I/O, parsing, or reporting concern.  Every other unit points
  inward at these types.

  Blaise idioms used here:
    * ARC - no manual Free; objects die when the last reference drops.
    * A managed record (TSourceLocation) for the pure value type; classes for
      the aggregates that flow through the pipeline by reference.
    * 1-based line and column, matching the compiler lexer's token positions
      (the language is 0-indexed, but diagnostics follow the editor convention
      the lexer already emits).  To read the raw text of a diagnostic's line
      from a 0-based TStringList of source lines, use Lines[Location.Line - 1]. }

unit Guard.Domain;

interface

uses
  SysUtils;

type
  { Ordered by increasing importance so severities can be compared numerically
    (Ord(sevError) > Ord(sevWarning)); the CLI --fail-on threshold relies on
    that ordering. }
  TSeverity = (
    sevInfo,
    sevWarning,
    sevError
  );

  { A span of source text.  Line and Col are 1-based (as the Blaise lexer
    reports them); Len is the length of the offending token/region in
    characters, 0 when only a point location is known. }
  TSourceLocation = record
    FileName: string;
    Line:     Integer;
    Col:      Integer;
    Len:      Integer;
  end;

  { An optional, structured "how to fix it" attached to a diagnostic.  Title is
    a human sentence; Replacement is the suggested source text for the span the
    owning diagnostic points at.  HasReplacement distinguishes an advisory-only
    fix (Title, no code) from a concrete text substitution. }
  TQuickFix = class
  public
    Title:          string;
    Replacement:    string;
    HasReplacement: Boolean;
    constructor Create(const ATitle: string); overload;
    constructor Create(const ATitle, AReplacement: string); overload;
  end;

  { One finding.  Immutable once built; the engine collects these into a
    TReport.  Fix is nil when the rule offers no quick-fix. }
  TDiagnostic = class
  public
    RuleId:   string;       { e.g. 'BL-1001' }
    Message:  string;       { concise description of the issue }
    Severity: TSeverity;
    Location: TSourceLocation;
    Fix:      TQuickFix;    { owned via ARC; nil = no suggestion }
    constructor Create(const ARuleId, AMessage: string;
                       ASeverity: TSeverity;
                       const ALocation: TSourceLocation);
  end;

{ ---- Severity helpers ---- }

{ Lower-case wire form used in JSON/XML reports and config files. }
function SeverityToStr(ASeverity: TSeverity): string;

{ Parse a severity name (case-insensitive: info/warning/error).  Returns True
  and sets AOut on success; False leaves AOut untouched. }
function TryParseSeverity(const AText: string; out AOut: TSeverity): Boolean;

{ Convenience: build a point location (no length) in one call. }
function SourceLoc(const AFileName: string; ALine, ACol: Integer): TSourceLocation; overload;
function SourceLoc(const AFileName: string; ALine, ACol, ALen: Integer): TSourceLocation; overload;

implementation

constructor TQuickFix.Create(const ATitle: string);
begin
  inherited Create();
  Title          := ATitle;
  Replacement    := '';
  HasReplacement := False;
end;

constructor TQuickFix.Create(const ATitle, AReplacement: string);
begin
  inherited Create();
  Title          := ATitle;
  Replacement    := AReplacement;
  HasReplacement := True;
end;

constructor TDiagnostic.Create(const ARuleId, AMessage: string;
  ASeverity: TSeverity; const ALocation: TSourceLocation);
begin
  inherited Create();
  RuleId   := ARuleId;
  Message  := AMessage;
  Severity := ASeverity;
  Location := ALocation;
  Fix      := nil;
end;

function SeverityToStr(ASeverity: TSeverity): string;
begin
  case ASeverity of
    sevInfo:    Result := 'info';
    sevWarning: Result := 'warning';
    sevError:   Result := 'error';
  else
    Result := 'info';
  end;
end;

function TryParseSeverity(const AText: string; out AOut: TSeverity): Boolean;
var
  L: string;
begin
  L := LowerCase(Trim(AText));
  Result := True;
  if L = 'info' then
    AOut := sevInfo
  else if L = 'warning' then
    AOut := sevWarning
  else if L = 'error' then
    AOut := sevError
  else
    Result := False;
end;

function SourceLoc(const AFileName: string; ALine, ACol: Integer): TSourceLocation;
begin
  Result.FileName := AFileName;
  Result.Line     := ALine;
  Result.Col      := ACol;
  Result.Len      := 0;
end;

function SourceLoc(const AFileName: string; ALine, ACol, ALen: Integer): TSourceLocation;
begin
  Result.FileName := AFileName;
  Result.Line     := ALine;
  Result.Col      := ACol;
  Result.Len      := ALen;
end;

end.
