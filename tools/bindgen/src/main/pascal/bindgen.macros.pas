{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — the macro-constants pass.

  #define constants are invisible in the AST (the preprocessor has
  already substituted them), yet they ARE the API for many C libraries
  (all of X11's event types and masks live in X.h as #defines).  They
  are recovered in two steps:

    1. 'clang -E -dD' re-preprocesses the header but RETAINS #define
       directives, with '# <line> "<file>"' linemarkers giving file
       attribution, so the same --match filter applies.  ParseDefines
       collects object-like macros (function-like ones are skipped —
       they are code, not constants).

    2. Macro bodies are arbitrary C expressions, possibly referencing
       other macros ('(1L<<15)', '(SAMPLE_A | SAMPLE_MASK)').  Instead
       of reimplementing the preprocessor, BuildProbeSource writes a
       probe translation unit with one
           static const long long __bgm_NAME = (long long)(NAME);
       per candidate and clang AST-dumps it: clang substitutes and
       type-checks everything, and EvalExprNode constant-folds the
       initialiser's expression tree (clang's C mode does not evaluate
       it in the JSON).  A macro that is not an integer constant (a
       type alias, a function reference) produces an error line in the
       probe — clang still dumps the rest, the entry just stays
       valueless and is not emitted.

  String-literal macros are taken directly from the define body. }

unit Bindgen.Macros;

interface

uses
  SysUtils, StrUtils, classes, generics.collections,
  Json.Types, Json.Reader,
  Bindgen.Model;

type
  TCMacro = class(TCDecl)
  public
    Name: string;
    Body: string;          { raw #define body, trimmed }
    IsString: Boolean;     { body is a plain "..." literal }
    StrValue: string;
    HasValue: Boolean;     { integer value successfully folded }
    Value: Int64;
    constructor Create(const AName, ABody: string);
  end;

{ Collect object-like macros from 'clang -E -dD' output.  AFileMatch is
  the same comma-separated substring filter the AST loader uses. }
function ParseDefines(const ADefinesText: string;
  const AFileMatch: string): TList<TCMacro>;

{ The probe translation unit for the integer candidates in AMacros. }
function BuildProbeSource(const AHeaderPath: string;
  AMacros: TList<TCMacro>): string;

{ Fold each __bgm_<name> initialiser in the probe's AST dump into the
  matching macro's Value.  Unfoldable entries are left valueless. }
procedure HarvestProbeValues(const AProbeJsonText: string;
  AMacros: TList<TCMacro>);

{ Constant-fold a clang expression node (IntegerLiteral, unary/binary
  operators, parens, integral casts).  False when the tree contains
  anything non-constant. }
function EvalExprNode(ANode: TJSONData; var AValue: Int64): Boolean;

implementation

constructor TCMacro.Create(const AName, ABody: string);
begin
  inherited Create();
  Name := AName;
  Body := ABody;
end;

function IsIdentByte(AB: Int): Boolean;
begin
  Result := ((AB >= Ord('A')) and (AB <= Ord('Z'))) or
            ((AB >= Ord('a')) and (AB <= Ord('z'))) or
            ((AB >= Ord('0')) and (AB <= Ord('9'))) or
            (AB = Ord('_'));
end;

function MatchesAnyFile(const AFile: string; AMatches: TList<String>): Boolean;
var
  I: Int;
begin
  Result := AMatches.Count = 0;
  for I := 0 to AMatches.Count - 1 do
    if Pos(AMatches[I], AFile) >= 0 then
    begin
      Result := True;
      Exit;
    end;
end;

{ Extract the quoted path from a '# <line> "<file>" ...' linemarker. }
function LineMarkerFile(const ALine: string): string;
var
  Q1, Q2: Int;
begin
  Result := '';
  Q1 := Pos('"', ALine);
  if Q1 < 0 then Exit;
  Q2 := PosEx('"', ALine, Q1 + 1);
  if Q2 < 0 then Exit;
  Result := MidStr(ALine, Q1 + 1, Q2 - Q1 - 1);
end;

function ParseDefines(const ADefinesText: string;
  const AFileMatch: string): TList<TCMacro>;
var
  Lines: TList<String>;
  Matches: TList<String>;
  ByName: TDictionary<string, TCMacro>;
  CurFile: string;
  I, P: Int;
  Line, Rest, Name, Body: string;
  M: TCMacro;
begin
  Result := TList<TCMacro>.Create();
  if AFileMatch = '' then
    Matches := TList<String>.Create()
  else
    Matches := SplitChar(AFileMatch, Ord(','));
  ByName := TDictionary<string, TCMacro>.Create();
  Lines := SplitLines(ADefinesText);
  CurFile := '';
  for I := 0 to Lines.Count - 1 do
  begin
    Line := Lines[I];
    if StartsStr('# ', Line) then
    begin
      Rest := LineMarkerFile(Line);
      if Rest <> '' then
        CurFile := Rest;
      Continue;
    end;
    if StartsStr('#undef ', Line) then
    begin
      Name := Trim(MidStr(Line, 7, Length(Line)));
      if ByName.ContainsKey(Name) then
        ByName.Remove(Name);
      Continue;
    end;
    if not StartsStr('#define ', Line) then Continue;
    if not MatchesAnyFile(CurFile, Matches) then Continue;
    Rest := Trim(MidStr(Line, 8, Length(Line)));
    { Name runs to the first non-identifier byte. }
    P := 0;
    while (P < Length(Rest)) and IsIdentByte(Rest[P]) do
      P := P + 1;
    if P = 0 then Continue;
    Name := LeftStr(Rest, P);
    if Name[0] = Ord('_') then Continue;         { implementation names }
    if (P < Length(Rest)) and (Rest[P] = Ord('(')) then Continue; { function-like }
    Body := Trim(MidStr(Rest, P, Length(Rest)));
    if Body = '' then Continue;                  { include guards etc. }
    { C semantics: a redefinition wins. }
    if ByName.ContainsKey(Name) then
      ByName.Remove(Name);
    M := TCMacro.Create(Name, Body);
    if (Length(Body) >= 2) and (Body[0] = Ord('"')) and
       (Body[Length(Body) - 1] = Ord('"')) and (Pos('\', Body) < 0) then
    begin
      M.IsString := True;
      M.StrValue := MidStr(Body, 1, Length(Body) - 2);
    end;
    ByName.Add(Name, M);
    Result.Add(M);
  end;
  { Drop entries that a later #undef removed. }
  for I := Result.Count - 1 downto 0 do
    if not ByName.ContainsKey(Result[I].Name) then
      Result.Delete(I);
end;

function BuildProbeSource(const AHeaderPath: string;
  AMacros: TList<TCMacro>): string;
var
  Lines: TStringList;
  I: Int;
begin
  Lines := TStringList.Create();
  Lines.Add('#include "' + AHeaderPath + '"');
  for I := 0 to AMacros.Count - 1 do
    if not AMacros[I].IsString then
      Lines.Add('static const long long __bgm_' + AMacros[I].Name +
        ' = (long long)(' + AMacros[I].Name + ');');
  Result := Lines.Text;
end;

function GetKind(ANode: TJSONData): string;
var
  K: TJSONData;
begin
  Result := '';
  if not (ANode is TJSONObject) then Exit;
  K := TJSONObject(ANode).Find('kind');
  if K <> nil then
    Result := K.AsString;
end;

{ First child expression node, skipping doc-comment children. }
function FirstInner(ANode: TJSONData): TJSONData;
var
  Inner: TJSONData;
begin
  Result := nil;
  if not (ANode is TJSONObject) then Exit;
  Inner := TJSONObject(ANode).Find('inner');
  if (Inner is TJSONArray) and (TJSONArray(Inner).Count > 0) then
    Result := TJSONArray(Inner)[0];
end;

function EvalExprNode(ANode: TJSONData; var AValue: Int64): Boolean;
var
  Obj: TJSONObject;
  Kind: string;
  Op: string;
  V, L, R: Int64;
  D: TJSONData;
  Inner: TJSONData;
  Arr: TJSONArray;
begin
  Result := False;
  if not (ANode is TJSONObject) then Exit;
  Obj := TJSONObject(ANode);
  Kind := GetKind(ANode);

  if (Kind = 'IntegerLiteral') or (Kind = 'CharacterLiteral') then
  begin
    D := Obj.Find('value');
    if D = nil then Exit;
    { The value can arrive as a JSON string or number; either way the
      text must parse as a signed 64-bit value.  Two different
      sentinels detect an unparseable (e.g. > High(Int64)) literal. }
    V := StrToInt64Def(D.AsString, -1);
    if (V = -1) and (StrToInt64Def(D.AsString, 0) = 0) and
       (D.AsString <> '-1') then Exit;
    AValue := V;
    Result := True;
    Exit;
  end;

  if Kind = 'ConstantExpr' then
  begin
    D := Obj.Find('value');
    if D <> nil then
    begin
      V := StrToInt64Def(D.AsString, -1);
      if (V = -1) and (StrToInt64Def(D.AsString, 0) = 0) and
         (D.AsString <> '-1') then Exit;
      AValue := V;
      Result := True;
      Exit;
    end;
    Result := EvalExprNode(FirstInner(ANode), AValue);
    Exit;
  end;

  if (Kind = 'ParenExpr') or (Kind = 'ImplicitCastExpr') or
     (Kind = 'CStyleCastExpr') then
  begin
    Result := EvalExprNode(FirstInner(ANode), AValue);
    Exit;
  end;

  if Kind = 'UnaryOperator' then
  begin
    D := Obj.Find('opcode');
    if D = nil then Exit;
    Op := D.AsString;
    if not EvalExprNode(FirstInner(ANode), V) then Exit;
    if Op = '-' then AValue := -V
    else if Op = '+' then AValue := V
    else if Op = '~' then AValue := V xor Int64(-1)
    else Exit;
    Result := True;
    Exit;
  end;

  if Kind = 'BinaryOperator' then
  begin
    D := Obj.Find('opcode');
    if D = nil then Exit;
    Op := D.AsString;
    Inner := Obj.Find('inner');
    if not (Inner is TJSONArray) then Exit;
    Arr := TJSONArray(Inner);
    if Arr.Count <> 2 then Exit;
    if not EvalExprNode(Arr[0], L) then Exit;
    if not EvalExprNode(Arr[1], R) then Exit;
    if Op = '+' then AValue := L + R
    else if Op = '-' then AValue := L - R
    else if Op = '*' then AValue := L * R
    else if Op = '/' then
    begin
      if R = 0 then Exit;
      AValue := L div R;
    end
    else if Op = '%' then
    begin
      if R = 0 then Exit;
      AValue := L mod R;
    end
    else if Op = '<<' then AValue := L shl R
    else if Op = '>>' then AValue := L shr R
    else if Op = '|' then AValue := L or R
    else if Op = '&' then AValue := L and R
    else if Op = '^' then AValue := L xor R
    else Exit;
    Result := True;
    Exit;
  end;
end;

procedure HarvestProbeValues(const AProbeJsonText: string;
  AMacros: TList<TCMacro>);
var
  Root: TJSONData;
  Inner: TJSONData;
  Arr: TJSONArray;
  I, J: Int;
  Node: TJSONObject;
  NameD: TJSONData;
  Name: string;
  V: Int64;
begin
  Root := GetJSON(AProbeJsonText);
  if not (Root is TJSONObject) then Exit;
  Inner := TJSONObject(Root).Find('inner');
  if not (Inner is TJSONArray) then Exit;
  Arr := TJSONArray(Inner);
  for I := 0 to Arr.Count - 1 do
  begin
    if GetKind(Arr[I]) <> 'VarDecl' then Continue;
    Node := TJSONObject(Arr[I]);
    NameD := Node.Find('name');
    if NameD = nil then Continue;
    Name := NameD.AsString;
    if not StartsStr('__bgm_', Name) then Continue;
    Name := MidStr(Name, 6, Length(Name));
    if not EvalExprNode(FirstInner(Node), V) then Continue;
    for J := 0 to AMacros.Count - 1 do
      if AMacros[J].Name = Name then
      begin
        AMacros[J].HasValue := True;
        AMacros[J].Value := V;
        Break;
      end;
  end;
end;

end.
