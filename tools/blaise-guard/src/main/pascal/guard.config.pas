{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - rule configuration.

  Holds the per-rule settings a run is driven by: whether a rule is enabled, an
  optional severity override, and a bag of named thresholds (e.g. maxLength).
  The domain deliberately does NOT depend on JSON - the loader stringifies JSON
  scalars into a plain name->value map, and rules read typed values back
  through GetInt/GetBool/GetStr with their own built-in defaults.  That keeps
  the config format swappable (a future TOML/XML loader would target the same
  TGuardConfig).

  Config file shape (blaise-guard.json):

    {
      "rules": {
        "BL-1001": { "enabled": true, "severity": "warning",
                     "params": { "maxLength": 120 } },
        "BL-1002": { "enabled": true, "params": { "maxLines": 15 } }
      }
    }

  A rule absent from the file gets a default-enabled TRuleConfig (Null Object),
  so rules never have to nil-check. }

unit Guard.Config;

interface

uses
  SysUtils,
  Generics.Collections,
  Json.Types,
  Json.Reader,
  Guard.Domain;

type
  TRuleConfig = class
  private
    FEnabled:          Boolean;
    FHasSeverity:      Boolean;
    FSeverity:         TSeverity;
    FParams:           TDictionary<string, string>;
  public
    constructor Create;

    procedure SetParam(const AName, AValue: string);

    { Typed reads.  Return ADefault when the param is absent or unparseable, so
      each rule owns the authoritative default for its own threshold. }
    function GetInt(const AName: string; ADefault: Integer): Integer;
    function GetBool(const AName: string; ADefault: Boolean): Boolean;
    function GetStr(const AName, ADefault: string): string;

    property Enabled:     Boolean read FEnabled write FEnabled;
    property HasSeverity: Boolean read FHasSeverity write FHasSeverity;
    property Severity:    TSeverity read FSeverity write FSeverity;
  end;

  TGuardConfig = class
  private
    FRules:          TDictionary<string, TRuleConfig>;
    FDefaultEnabled: Boolean;
  public
    constructor Create;

    { Look up (or lazily create) the config for a rule id.  Always returns a
      usable object - a rule with no explicit entry is enabled with no
      overrides. }
    function RuleConfig(const ARuleId: string): TRuleConfig;

    { Effective severity for a diagnostic: the rule's config override when set,
      otherwise the severity the rule itself proposes. }
    function EffectiveSeverity(const ARuleId: string;
                               ARuleDefault: TSeverity): TSeverity;

    function IsEnabled(const ARuleId: string): Boolean;

    { When False, a rule with no explicit entry is treated as disabled
      (allowlist mode).  Tests use this to exercise one rule in isolation;
      defaults to True (every rule on unless turned off). }
    property DefaultEnabled: Boolean read FDefaultEnabled write FDefaultEnabled;

    { Build the default (empty) configuration: every rule enabled at its own
      built-in threshold and severity. }
    class function Default: TGuardConfig;

    { Parse a blaise-guard.json document.  Raises EGuardConfigError on
      malformed JSON or an unexpected shape. }
    class function LoadFromString(const AJson: string): TGuardConfig;
    class function LoadFromFile(const APath: string): TGuardConfig;
  end;

  EGuardConfigError = class(Exception);

implementation

uses
  Classes;

{ ---- TRuleConfig ---- }

constructor TRuleConfig.Create;
begin
  inherited Create();
  FEnabled     := True;
  FHasSeverity := False;
  FSeverity    := sevWarning;
  FParams      := TDictionary<string, string>.Create();
end;

procedure TRuleConfig.SetParam(const AName, AValue: string);
begin
  FParams.Add(AName, AValue);   { TDictionary.Add is an upsert }
end;

function TRuleConfig.GetInt(const AName: string; ADefault: Integer): Integer;
var
  Raw: string;
begin
  { StrToIntDef yields ADefault for both an absent and an unparseable value. }
  if FParams.TryGetValue(AName, Raw) then
    Result := StrToIntDef(Trim(Raw), ADefault)
  else
    Result := ADefault;
end;

function TRuleConfig.GetBool(const AName: string; ADefault: Boolean): Boolean;
var
  Raw: string;
begin
  if not FParams.TryGetValue(AName, Raw) then
    Exit(ADefault);
  Raw := LowerCase(Trim(Raw));
  if (Raw = 'true') or (Raw = '1') or (Raw = 'yes') then
    Result := True
  else if (Raw = 'false') or (Raw = '0') or (Raw = 'no') then
    Result := False
  else
    Result := ADefault;
end;

function TRuleConfig.GetStr(const AName, ADefault: string): string;
var
  Raw: string;
begin
  if FParams.TryGetValue(AName, Raw) then
    Result := Raw
  else
    Result := ADefault;
end;

{ ---- TGuardConfig ---- }

constructor TGuardConfig.Create;
begin
  inherited Create();
  FRules          := TDictionary<string, TRuleConfig>.Create();
  FDefaultEnabled := True;
end;

function TGuardConfig.RuleConfig(const ARuleId: string): TRuleConfig;
var
  RC: TRuleConfig;
begin
  if FRules.TryGetValue(ARuleId, RC) then
    Exit(RC);
  RC := TRuleConfig.Create();
  FRules.Add(ARuleId, RC);   { TDictionary.Add is an upsert }
  Result := RC;
end;

function TGuardConfig.EffectiveSeverity(const ARuleId: string;
  ARuleDefault: TSeverity): TSeverity;
var
  RC: TRuleConfig;
begin
  if FRules.TryGetValue(ARuleId, RC) and RC.HasSeverity then
    Result := RC.Severity
  else
    Result := ARuleDefault;
end;

function TGuardConfig.IsEnabled(const ARuleId: string): Boolean;
var
  RC: TRuleConfig;
begin
  if FRules.TryGetValue(ARuleId, RC) then
    Result := RC.Enabled
  else
    Result := FDefaultEnabled;   { unlisted follows the default policy }
end;

class function TGuardConfig.Default: TGuardConfig;
begin
  Result := TGuardConfig.Create();
  { BL-1004 (UnusedIdentifiers) is heuristic (closures/shadowing), so the
    built-in default posture leaves it off; a config file can turn it on. }
  Result.RuleConfig('BL-1004').Enabled := False;
end;

class function TGuardConfig.LoadFromString(const AJson: string): TGuardConfig;
var
  Cfg:      TGuardConfig;
  Root:     TJSONData;
  RulesObj: TJSONObject;
  RuleNode: TJSONData;
  RuleObj:  TJSONObject;
  ParamsObj: TJSONObject;
  Sev:      TSeverity;
  RC:       TRuleConfig;
  I, P:     Integer;
  RuleId:   string;
begin
  Cfg := TGuardConfig.Create();
  try
    Root := GetJSON(AJson);
  except
    on E: Exception do
      raise EGuardConfigError.Create('Invalid JSON config: ' + E.Message);
  end;

  if Root.GetJSONType <> jtObject then
    raise EGuardConfigError.Create('Config root must be a JSON object');

  RuleNode := TJSONObject(Root).Find('rules');
  if RuleNode = nil then
    Exit(Cfg);   { a config with no "rules" block leaves all defaults in place }
  if RuleNode.GetJSONType <> jtObject then
    raise EGuardConfigError.Create('"rules" must be a JSON object');

  RulesObj := TJSONObject(RuleNode);
  for I := 0 to RulesObj.GetCount - 1 do
  begin
    RuleId := RulesObj.GetName(I);
    if RulesObj.ItemsByIndex[I].GetJSONType <> jtObject then
      Continue;
    RuleObj := TJSONObject(RulesObj.ItemsByIndex[I]);
    RC := Cfg.RuleConfig(RuleId);

    if RuleObj.Contains('enabled') then
      RC.Enabled := RuleObj.Find('enabled').AsBoolean;

    if RuleObj.Contains('severity') then
      if TryParseSeverity(RuleObj.Find('severity').AsString, Sev) then
      begin
        RC.Severity    := Sev;
        RC.HasSeverity := True;
      end;

    if RuleObj.Contains('params') and
       (RuleObj.Find('params').GetJSONType = jtObject) then
    begin
      ParamsObj := TJSONObject(RuleObj.Find('params'));
      for P := 0 to ParamsObj.GetCount - 1 do
        RC.SetParam(ParamsObj.GetName(P),
                    ParamsObj.ItemsByIndex[P].GetAsString);
    end;
  end;

  Result := Cfg;
end;

class function TGuardConfig.LoadFromFile(const APath: string): TGuardConfig;
var
  SL: TStringList;
begin
  SL := TStringList.Create();
  SL.LoadFromFile(APath);
  Result := LoadFromString(SL.Text);
end;

end.
