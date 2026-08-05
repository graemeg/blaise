{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - the rule seam: the IRule port, the per-file context, the three
  Template-Method base classes rules extend, and the self-registration
  registry.

  Design patterns at work here:
    * Strategy / plugin port - IRule is a GUID-less interface; every rule is
      one, so the engine depends only on the abstraction.
    * Template Method - TLineRuleBase / TTokenRuleBase / TAstRuleBase implement
      the invariant "how to traverse" (lines, tokens, AST) and leave the
      "what to check" to a single overridable hook.
    * Registry + self-registration - each rule unit calls RegisterRule in its
      initialization section, exactly like blaise.testing's RegisterTest, so
      adding a rule is a one-line, decoupled act. }

unit Guard.Rules;

interface

uses
  SysUtils,
  Generics.Collections,
  uLexer,
  uAST,
  Guard.Domain,
  Guard.Report,
  Guard.Config,
  Guard.Frontend,
  Guard.Ast.Walker;

type
  { One rule's working set for one file, plus the emit sink.  Borrows the
    model/config/report (marked [Unretained]) - it does not own them. }
  TRuleContext = class
  private
    [Unretained] FModel:    TSourceModel;
    [Unretained] FRuleCfg:  TRuleConfig;
    [Unretained] FReport:   TReport;
    FRuleId:   string;
    FSeverity: TSeverity;
  public
    constructor Create(const ARuleId: string; AModel: TSourceModel;
                       ARuleCfg: TRuleConfig; AReport: TReport;
                       ASeverity: TSeverity);

    { Emit a finding at this rule's effective severity, optionally with a
      structured quick-fix.  Both overloads honour inline suppression — see
      IsSuppressed. }
    procedure Emit(const AMessage: string; const ALoc: TSourceLocation); overload;
    procedure Emit(const AMessage: string; const ALoc: TSourceLocation;
                   AFix: TQuickFix); overload;

    { True when the source asks for this finding to be ignored, via a comment
      on the offending line or on the line immediately above it:

        X := Y;   // blaise-guard: ignore              — all rules, this line
        X := Y;   // blaise-guard: ignore BL-2003      — that rule only
        // blaise-guard: ignore BL-2003 BL-1003        — next line, two rules

      Rationale for the shape: SonarQube's bare `// NOSONAR` suppresses
      EVERYTHING on the line, which silently hides later, unrelated findings.
      Naming the rule is the common case here, so an unqualified `ignore` is
      allowed but deliberately blunt.  A reason may follow a `-` and is
      ignored by the parser but is the point of writing one:

        // blaise-guard: ignore BL-2003 - FA[1] is the second OPERAND }
    function IsSuppressed(const ALoc: TSourceLocation): Boolean;
  private
    { Shared matcher: does ALine carry AMarker with a rule list covering
      FRuleId (or no list at all, meaning every rule)? }
    function MarkerCovers(const ALine, AMarker: string): Boolean;
    { True when one source line carries a line-scoped directive. }
    function LineSuppresses(const ALine: string): Boolean;
    { True when one header line carries a FILE-scoped directive. }
    function FileSuppresses(const ALine: string): Boolean;
  public

    property Model:   TSourceModel read FModel;
    property RuleCfg: TRuleConfig read FRuleCfg;
    property RuleId:  string read FRuleId;
  end;

  { The extensibility port.  GUID-less, as Blaise interfaces need no IID.

    Lifecycle per analysis run:
      Reset            once, before any file
      Analyse(ctx)     once per file (ctx carries that file's model)
      Finalize(ctx)    once, after every file (ctx has a nil Model)

    Reset/Finalize let a cross-file rule (e.g. duplicate detection) accumulate
    state across files and emit at the end.  Most rules are per-file and
    inherit the empty defaults. }
  IRule = interface
    function Id: string;                  { stable identifier, e.g. 'BL-1001' }
    function Name: string;                { short human-readable name }
    function DefaultSeverity: TSeverity;  { severity when config gives no override }
    procedure Reset;
    procedure Analyse(AContext: TRuleContext);
    procedure Finalize(AContext: TRuleContext);
  end;

  { Common storage + IRule plumbing shared by every base flavour. }
  TRuleBase = class(IRule)
  protected
    FId:       string;
    FName:     string;
    FSeverity: TSeverity;
  public
    function Id: string;
    function Name: string;
    function DefaultSeverity: TSeverity;
    procedure Reset; virtual;                            { default: no-op }
    procedure Analyse(AContext: TRuleContext); virtual; abstract;
    procedure Finalize(AContext: TRuleContext); virtual; { default: no-op }
  end;

  { Line-oriented rule: the engine hands each source line to CheckLine.
    Runs even when parsing failed - it needs only Model.Lines. }
  TLineRuleBase = class(TRuleBase)
  protected
    { ALineNo is 1-based to match diagnostic line numbers. }
    procedure CheckLine(AContext: TRuleContext; const ALine: string;
                        ALineNo: Integer); virtual; abstract;
  public
    procedure Analyse(AContext: TRuleContext); override;
  end;

  { Token-oriented rule: the engine hands the whole token stream to
    CheckTokens.  Also parse-failure tolerant (the lexer runs regardless). }
  TTokenRuleBase = class(TRuleBase)
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); virtual; abstract;
  public
    procedure Analyse(AContext: TRuleContext); override;
  end;

  { AST-oriented rule: itself a visitor (so it overrides only the node hooks it
    cares about) whose Analyse template drives a walker over the file's top
    blocks.  Skipped when the file did not parse. }
  TAstRuleBase = class(TAstVisitor, IRule)
  protected
    FId:       string;
    FName:     string;
    FSeverity: TSeverity;
    [Unretained] FCtx: TRuleContext;   { valid only during Analyse }
    procedure Emit(const AMessage: string; const ALoc: TSourceLocation);
  public
    function Id: string;
    function Name: string;
    function DefaultSeverity: TSeverity;
    procedure Reset; virtual;                            { default: no-op }
    procedure Analyse(AContext: TRuleContext);
    procedure Finalize(AContext: TRuleContext); virtual; { default: no-op }
  end;

{ ---- Registry (self-registration) ---- }

{ Register a rule instance.  Called from each rule unit's initialization
  section; the registry keeps the instance alive via ARC. }
procedure RegisterRule(ARule: IRule);
function  RegisteredRuleCount: Integer;
function  RegisteredRule(AIndex: Integer): IRule;

implementation

const
  { Inline suppression marker.  Lowercase — the line is folded before matching,
    so the directive may be written in any case.  Deliberately namespaced
    rather than a bare word like NOSONAR: it says which tool it addresses, and
    it cannot collide with prose. }
  SUPPRESS_MARKER      = 'blaise-guard: ignore';
  { Distinct marker, deliberately NOT a prefix-match of the line form, so a
    line directive in the header keeps its line-only meaning. }
  SUPPRESS_FILE_MARKER = 'blaise-guard: ignore-file';

var
  GRules: TList<IRule>;

{ ---- TRuleContext ---- }

constructor TRuleContext.Create(const ARuleId: string; AModel: TSourceModel;
  ARuleCfg: TRuleConfig; AReport: TReport; ASeverity: TSeverity);
begin
  inherited Create();
  FRuleId   := ARuleId;
  FModel    := AModel;
  FRuleCfg  := ARuleCfg;
  FReport   := AReport;
  FSeverity := ASeverity;
end;

{ Does ALine carry a suppression directive covering FRuleId?  The marker is
  matched case-insensitively anywhere in the line, so it works after code, in
  a // comment, or inside a brace comment. }
function TRuleContext.MarkerCovers(const ALine, AMarker: string): Boolean;
var
  Low, Rest: string;
  P, IdP:    Integer;
begin
  Result := False;
  Low := LowerCase(ALine);
  P := Pos(AMarker, Low);
  if P < 0 then Exit;

  Rest := Copy(Low, P + Length(AMarker), Length(Low) - P - Length(AMarker) + 1);

  { A reason after the separator is prose, not rule ids — cut it off first so
    a stray id-looking word in the reason cannot widen the suppression.  Rule
    ids themselves contain '-' (bl-2003), so the separator is a SPACED ' - '. }
  IdP := Pos(' - ', Rest);
  if IdP >= 0 then
    Rest := Copy(Rest, 0, IdP);

  { No id listed => suppress every rule on this line. }
  if Trim(Rest) = '' then
    Exit(True);

  Result := Pos(LowerCase(FRuleId), Rest) >= 0;
end;

function TRuleContext.LineSuppresses(const ALine: string): Boolean;
begin
  { 'ignore' is a PREFIX of 'ignore-file', so a bare MarkerCovers check would
    make a file-scoped directive also read as a line-scoped one.  A file
    directive is not a line directive: defer to FileSuppresses for those. }
  if Self.FileSuppresses(ALine) then Exit(False);
  Result := Self.MarkerCovers(ALine, SUPPRESS_MARKER);
end;

function TRuleContext.FileSuppresses(const ALine: string): Boolean;
begin
  Result := Self.MarkerCovers(ALine, SUPPRESS_FILE_MARKER);
end;

function TRuleContext.IsSuppressed(const ALoc: TSourceLocation): Boolean;
var
  Idx, K, Scan: Integer;
  Low:          string;
begin
  Result := False;
  if FModel = nil then Exit;          { cross-file Finalize phase: no line }
  if FModel.Lines = nil then Exit;

  { FILE-level directive: `blaise-guard: ignore-file BL-XXXX` anywhere in the
    header comment covers every finding in the file.  It uses a DISTINCT
    marker rather than reusing the line form, because a line-form directive
    inside the header must keep meaning "this line only" — 26 findings in this
    tree legitimately land on lines 1-15.

    This exists because one mis-inferred declaration can produce dozens of
    findings: `FA: array of TA64Op` accounts for 85 BL-2003 hits in a single
    unit, and the token-level rule cannot see that FA is not a string. }
  { Scan the file's PREAMBLE only — everything before the first line that
    starts a declaration section.  A file directive belongs in a header
    comment; bounding the scan (rather than using a fixed line count) means a
    directive further down cannot silently acquire file scope, and early CODE
    lines stay eligible for ordinary line-scoped suppression.

    The boundary is `interface` / `implementation` / the first declaration
    keyword, NOT the `unit` line: house style in this codebase puts the
    descriptive comment AFTER `unit <name>;`, so stopping at `unit` would miss
    the natural place to write the directive. }
  Scan := FModel.Lines.Count;
  for K := 0 to FModel.Lines.Count - 1 do
  begin
    Low := LowerCase(Trim(FModel.Lines.Strings[K]));
    if (Low = 'interface') or (Low = 'implementation') or (Low = 'begin') or
       (Pos('uses ', Low) = 0) or (Low = 'uses') or
       (Pos('var ', Low) = 0) or (Low = 'var') or
       (Pos('type ', Low) = 0) or (Low = 'type') or
       (Pos('const ', Low) = 0) or (Low = 'const') then
    begin
      Scan := K;
      break;
    end;
  end;
  for K := 0 to Scan - 1 do
    if Self.FileSuppresses(FModel.Lines.Strings[K]) then
      Exit(True);
  { TSourceLocation.Line is 1-based; Lines is 0-based. }
  Idx := ALoc.Line - 1;
  if (Idx < 0) or (Idx >= FModel.Lines.Count) then Exit;

  { The offending line itself... }
  if Self.LineSuppresses(FModel.Lines.Strings[Idx]) then
    Exit(True);
  { ...or the line above it, for findings that point at a construct's first
    line where a trailing comment would be awkward (a case statement, a
    routine header). }
  if Idx > 0 then
    Result := Self.LineSuppresses(FModel.Lines.Strings[Idx - 1]);
end;

procedure TRuleContext.Emit(const AMessage: string; const ALoc: TSourceLocation);
begin
  if Self.IsSuppressed(ALoc) then Exit;
  FReport.Add(TDiagnostic.Create(FRuleId, AMessage, FSeverity, ALoc));
end;

procedure TRuleContext.Emit(const AMessage: string; const ALoc: TSourceLocation;
  AFix: TQuickFix);
var
  D: TDiagnostic;
begin
  if Self.IsSuppressed(ALoc) then
  begin
    AFix.Free();          { the caller handed us ownership }
    Exit;
  end;
  D := TDiagnostic.Create(FRuleId, AMessage, FSeverity, ALoc);
  D.Fix := AFix;
  FReport.Add(D);
end;

{ ---- TRuleBase ---- }

function TRuleBase.Id: string;                    begin Result := FId; end;
function TRuleBase.Name: string;                  begin Result := FName; end;
function TRuleBase.DefaultSeverity: TSeverity;    begin Result := FSeverity; end;
procedure TRuleBase.Reset;                        begin end;
procedure TRuleBase.Finalize(AContext: TRuleContext); begin end;

{ ---- TLineRuleBase ---- }

procedure TLineRuleBase.Analyse(AContext: TRuleContext);
var
  I: Integer;
begin
  for I := 0 to AContext.Model.Lines.Count - 1 do
    CheckLine(AContext, AContext.Model.Lines[I], I + 1);
end;

{ ---- TTokenRuleBase ---- }

procedure TTokenRuleBase.Analyse(AContext: TRuleContext);
begin
  CheckTokens(AContext, AContext.Model.Tokens);
end;

{ ---- TAstRuleBase ---- }

function TAstRuleBase.Id: string;                 begin Result := FId; end;
function TAstRuleBase.Name: string;               begin Result := FName; end;
function TAstRuleBase.DefaultSeverity: TSeverity; begin Result := FSeverity; end;
procedure TAstRuleBase.Reset;                     begin end;
procedure TAstRuleBase.Finalize(AContext: TRuleContext); begin end;

procedure TAstRuleBase.Emit(const AMessage: string; const ALoc: TSourceLocation);
begin
  if FCtx <> nil then
    FCtx.Emit(AMessage, ALoc);
end;

procedure TAstRuleBase.Analyse(AContext: TRuleContext);
var
  Walker:    TAstWalker;
  Primary:   TBlock;
  Secondary: TBlock;
begin
  { No usable tree when the parser failed - AST rules simply do not fire. }
  if not AContext.Model.ParseOk then
    Exit;
  FCtx := AContext;
  try
    Walker := TAstWalker.Create(Self);
    AContext.Model.TopBlocks(Primary, Secondary);
    Walker.Walk(Primary);
    Walker.Walk(Secondary);
  finally
    FCtx := nil;
  end;
end;

{ ---- Registry ---- }

procedure RegisterRule(ARule: IRule);
begin
  GRules.Add(ARule);
end;

function RegisteredRuleCount: Integer;
begin
  Result := GRules.Count;
end;

function RegisteredRule(AIndex: Integer): IRule;
begin
  Result := GRules[AIndex];
end;

initialization
  GRules := TList<IRule>.Create();

end.
