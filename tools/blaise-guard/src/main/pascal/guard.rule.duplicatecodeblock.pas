{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard rule BL-3001: DuplicateCodeBlock.

  A copy-paste detector (CPD).  It fingerprints every window of K consecutive
  tokens with a Rabin-Karp rolling hash, and reports a window whose fingerprint
  (and, on match, whose exact token sequence) has already been seen - anywhere
  in the codebase, not just the current file.

  This is the reference cross-file rule: it accumulates each file's token
  stream during the per-file Analyse pass and does the actual detection in
  Finalize, once every file has been seen.  Reset clears state so repeated runs
  in one process stay independent.

  Robustness: the hash is only a candidate filter.  Every fingerprint match is
  verified by an exact token comparison, so a hash collision (or any hashing
  imperfection) can never produce a false positive - at worst it would miss a
  duplicate.

  Config:
    rules."BL-3001".params.minTokens             window size K (default 30)
    rules."BL-3001".params.ignoreIdentifierNames when true, identifier spelling
                                                 is ignored so renamed clones
                                                 still match (default false). }

unit Guard.Rule.DuplicateCodeBlock;

interface

implementation

uses
  SysUtils,
  Generics.Collections,
  uLexer,
  Guard.Domain,
  Guard.Rules;

const
  RULE_ID          = 'BL-3001';
  RULE_NAME        = 'DuplicateCodeBlock';
  DEFAULT_MINTOKENS = 30;
  HASH_MOD          = 1000000007;   { prime; keeps products within Int64 }
  HASH_BASE         = 131;

type
  { One analysed file's retained token stream (kept alive across files via ARC
    so Finalize can verify and locate matches). }
  TDupFile = class
  public
    FileName: string;
    Tokens:   TList<TToken>;
    constructor Create(const AFileName: string; ATokens: TList<TToken>);
  end;

  { First place a given fingerprint was seen. }
  TWindowRef = class
  public
    FileIdx: Integer;
    Start:   Integer;
    constructor Create(AFileIdx, AStart: Integer);
  end;

  TDuplicateCodeBlockRule = class(TTokenRuleBase)
  private
    FFiles: TList<TDupFile>;
    function TokenHash(AKind: TTokenKind; const AValue: string;
                       AIgnoreNames: Boolean): Int64;
    function WindowsEqual(ATokensA: TList<TToken>; AStartA: Integer;
                          ATokensB: TList<TToken>; AStartB: Integer;
                          AK: Integer; AIgnoreNames: Boolean): Boolean;
  protected
    procedure CheckTokens(AContext: TRuleContext;
                          ATokens: TList<TToken>); override;
  public
    constructor Create;
    procedure Reset; override;
    procedure Finalize(AContext: TRuleContext); override;
  end;

{ ---- helper classes ---- }

constructor TDupFile.Create(const AFileName: string; ATokens: TList<TToken>);
begin
  inherited Create();
  FileName := AFileName;
  Tokens   := ATokens;
end;

constructor TWindowRef.Create(AFileIdx, AStart: Integer);
begin
  inherited Create();
  FileIdx := AFileIdx;
  Start   := AStart;
end;

{ ---- rule ---- }

constructor TDuplicateCodeBlockRule.Create;
begin
  inherited Create();
  FId       := RULE_ID;
  FName     := RULE_NAME;
  FSeverity := sevWarning;
  FFiles    := TList<TDupFile>.Create();
end;

procedure TDuplicateCodeBlockRule.Reset;
begin
  FFiles := TList<TDupFile>.Create();   { drop any prior run's state }
end;

procedure TDuplicateCodeBlockRule.CheckTokens(AContext: TRuleContext;
  ATokens: TList<TToken>);
begin
  { Retain this file's tokens for the cross-file Finalize pass. }
  FFiles.Add(TDupFile.Create(AContext.Model.FileName, ATokens));
end;

function TDuplicateCodeBlockRule.TokenHash(AKind: TTokenKind;
  const AValue: string; AIgnoreNames: Boolean): Int64;
var
  S: string;
  J: Integer;
  H: Int64;
begin
  S := IntToStr(Ord(AKind)) + '#';
  if not (AIgnoreNames and (AKind = tkIdent)) then
    S := S + AValue;
  H := 0;
  for J := 0 to Length(S) - 1 do
    H := (H * 257 + Byte(S[J])) mod HASH_MOD;
  Result := H;
end;

function TDuplicateCodeBlockRule.WindowsEqual(
  ATokensA: TList<TToken>; AStartA: Integer;
  ATokensB: TList<TToken>; AStartB: Integer;
  AK: Integer; AIgnoreNames: Boolean): Boolean;
var
  J: Integer;
  A, B: TToken;
begin
  for J := 0 to AK - 1 do
  begin
    A := ATokensA[AStartA + J];
    B := ATokensB[AStartB + J];
    if A.Kind <> B.Kind then
      Exit(False);
    if not (AIgnoreNames and (A.Kind = tkIdent)) then
      if A.Value <> B.Value then
        Exit(False);
  end;
  Result := True;
end;

procedure TDuplicateCodeBlockRule.Finalize(AContext: TRuleContext);
var
  K:            Integer;
  IgnoreNames:  Boolean;
  Map:          TDictionary<Int64, TWindowRef>;
  PowK:         Int64;
  J, Fi, I, N:  Integer;
  F:            TDupFile;
  T:            TList<TToken>;
  Th:           array of Int64;
  H, Tmp:       Int64;
  Ref:          TWindowRef;
  LastEmitEnd:  Integer;
  RefFile:      TDupFile;
  Matched:      Boolean;
begin
  K           := AContext.RuleCfg.GetInt('minTokens', DEFAULT_MINTOKENS);
  IgnoreNames := AContext.RuleCfg.GetBool('ignoreIdentifierNames', False);
  if K < 1 then
    Exit;

  Map := TDictionary<Int64, TWindowRef>.Create();

  { PowK = HASH_BASE^(K-1) mod HASH_MOD - the weight of the leftmost token. }
  PowK := 1;
  for J := 1 to K - 1 do
    PowK := (PowK * HASH_BASE) mod HASH_MOD;

  for Fi := 0 to FFiles.Count - 1 do
  begin
    F := FFiles[Fi];
    T := F.Tokens;

    { Usable token count excludes the terminating tkEOF. }
    N := T.Count;
    if (N > 0) and (T[N - 1].Kind = tkEOF) then
      Dec(N);
    if N < K then
      Continue;

    SetLength(Th, N);
    for J := 0 to N - 1 do
      Th[J] := TokenHash(T[J].Kind, T[J].Value, IgnoreNames);

    { Hash of the first window [0, K). }
    H := 0;
    for J := 0 to K - 1 do
      H := (H * HASH_BASE + Th[J]) mod HASH_MOD;

    LastEmitEnd := -1;
    I := 0;
    while True do
    begin
      { Nested (not short-circuit-dependent): only touch Ref once the key is
        known present. }
      Matched := False;
      if Map.TryGetValue(H, Ref) then
        if WindowsEqual(FFiles[Ref.FileIdx].Tokens, Ref.Start, T, I, K, IgnoreNames) then
          Matched := True;

      if Matched then
      begin
        { Suppress overlapping re-reports of the same duplicated region. }
        if I >= LastEmitEnd then
        begin
          RefFile := FFiles[Ref.FileIdx];
          AContext.Emit(
            'Duplicated block of ' + IntToStr(K) + ' tokens (first seen at ' +
            RefFile.FileName + ':' + IntToStr(RefFile.Tokens[Ref.Start].Line) + ')',
            SourceLoc(F.FileName, T[I].Line, T[I].Col));
          LastEmitEnd := I + K;
        end;
      end
      else if not Map.ContainsKey(H) then
        Map.Add(H, TWindowRef.Create(Fi, I));

      if I = N - K then
        Break;

      { Roll the hash from window I to I+1.  Arithmetic stays within Int64:
        Th[I]*PowK < 1e9*1e9 < 9.2e18; H*HASH_BASE < 1e9*131. }
      Tmp := (Th[I] * PowK) mod HASH_MOD;
      H := (H - Tmp) mod HASH_MOD;
      if H < 0 then
        H := H + HASH_MOD;
      H := (H * HASH_BASE) mod HASH_MOD;
      H := (H + Th[I + K]) mod HASH_MOD;
      Inc(I);
    end;
  end;
end;

initialization
  RegisterRule(TDuplicateCodeBlockRule.Create());

end.
