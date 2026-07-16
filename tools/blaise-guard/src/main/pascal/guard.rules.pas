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
      structured quick-fix. }
    procedure Emit(const AMessage: string; const ALoc: TSourceLocation); overload;
    procedure Emit(const AMessage: string; const ALoc: TSourceLocation;
                   AFix: TQuickFix); overload;

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

procedure TRuleContext.Emit(const AMessage: string; const ALoc: TSourceLocation);
begin
  FReport.Add(TDiagnostic.Create(FRuleId, AMessage, FSeverity, ALoc));
end;

procedure TRuleContext.Emit(const AMessage: string; const ALoc: TSourceLocation;
  AFix: TQuickFix);
var
  D: TDiagnostic;
begin
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
