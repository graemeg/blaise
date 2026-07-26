{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

(*
  FlagCoverage - verifies every semantic ANNOTATION FIELD on the AST node
  classes that codegen dispatches on is actually READ by each backend.

  THE BUG CLASS THIS EXISTS FOR
  -----------------------------
  uSemantic annotates AST nodes with flags that tell codegen which shape to
  emit (TFieldAccessExpr.IsCharAccess, .IsArrayAccess, .IsMethodCall, ...).
  Each backend must have an arm for each flag.  When one does not, the node
  falls through to a more general arm and the compiler emits plausible but
  WRONG code - silently, with no diagnostic:

    2026-07-26  arm64 IsCharAccess      Rec.Str[N] returned the data POINTER
    2026-07-26  arm64 IsArrayAccess     Rec.Arr[N] returned the data POINTER
    2026-07-26  qbe   IsCharAccess      A.B.Str[N] on a CHAINED base, ditto

  `grep IsCharAccess blaise.codegen.native.arm64.pas` returned NOTHING before
  the first of those was fixed.  Nothing asked that question, so three shipped
  in one week.  This tool asks it.

  WHAT IT DOES
  ------------
  For each watched class it collects the annotation fields declared in
  uAST.pas, then counts how many times `.Field` is referenced in each codegen
  unit (comments and string literals stripped).  The counts are compared
  against a checked-in status file.

  WHAT A COUNT CAN AND CANNOT TELL YOU  - read this before trusting output
  -----------------------------------------------------------------------
  Measured against the real bugs above, on the commits that had them:

    * IsCharAccess was 0 in the arm64 backend      -> a zero-check CATCHES it.
    * IsArrayAccess was 2 in the arm64 backend while the READ path was still
      missing (only the ADDRESS path used it)      -> a zero-check MISSES it.
    * IsMethodCall is 0 in the arm64 backend TODAY, yet `O.Inner.Hi()`
      compiles and lowers correctly there - the shape is handled through
      another route                                -> zero is NOT proof of a bug.

  So a count is a SIGNAL, not a verdict.  That is why the status file records
  an expected count per (class, field, backend) rather than a bare
  covered/uncovered bit: a DROP from the recorded count is the actionable
  event (an arm was deleted or a rename silently orphaned a flag), and a rise
  just needs the baseline refreshed.  `unused` marks a flag a backend
  deliberately never reads.

  This will not find every missing arm.  It makes the question askable, and it
  turns "nobody noticed for a week" into "the build told you the day it
  changed".

  USAGE
    flag-coverage            check against flag-coverage.status; exit 1 on drop
    flag-coverage --reset    regenerate the status file from current source
    flag-coverage --report   print the full count table, always exit 0

  Exit codes: 0 = clean, 1 = coverage regression, 2 = I/O error.
*)

program FlagCoverage;

uses
  SysUtils, Classes, contnrs, uStrCompat;

const
  AST_REL    = 'compiler/src/main/pascal/uAST.pas';
  ROOT_REL   = 'compiler/src/main/pascal/Blaise.pas';
  STATUS_REL = 'tools/flag-coverage/flag-coverage.status';

  { The codegen units a flag must be read by.  Keep the labels short - they
    are the status-file column names. }
  BACKEND_COUNT = 3;
  BackendLabel: array[0..2] of string = ('qbe', 'x86_64', 'arm64');
  BackendPath:  array[0..2] of string = (
    'compiler/src/main/pascal/blaise.codegen.qbe.pas',
    'compiler/src/main/pascal/blaise.codegen.native.x86_64.pas',
    'compiler/src/main/pascal/blaise.codegen.native.arm64.pas');

  { AST classes whose annotation fields drive a codegen dispatch.  Add a class
    here when it grows a flag that selects an emission shape. }
  WATCH_COUNT = 3;
  WatchClass: array[0..2] of string = (
    'TFieldAccessExpr', 'TAssignStmt', 'TMethodCallExpr');

type
  TFlagRow = class
  public
    ClsName:   string;
    FieldName: string;
    Counts:    array[0..2] of Integer;
    Expected:  array[0..2] of Integer;   { -1 = 'unused' }
    HasStatus: Boolean;
  end;

var
  Root:  string;
  Rows:  TObjectList;
  Hay:   array[0..2] of string;   { each backend's comment-stripped text }

{ ------------------------------------------------------------------ }
{ Small helpers                                                        }
{ ------------------------------------------------------------------ }

function FindProjectRoot(): string;
var
  Dir, Parent: string;
  I: Integer;
begin
  Dir := GetCurrentDir();
  for I := 0 to 6 do
  begin
    if FileExists(IncludeTrailingPathDelimiter(Dir) + AST_REL) and
       FileExists(IncludeTrailingPathDelimiter(Dir) + ROOT_REL) then
      Exit(IncludeTrailingPathDelimiter(Dir));
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := '';
end;

function IsIdentStart(C: Integer): Boolean;
begin
  Result := ((C >= 65) and (C <= 90)) or ((C >= 97) and (C <= 122)) or (C = 95);
end;

function IsIdentCont(C: Integer): Boolean;
begin
  Result := IsIdentStart(C) or ((C >= 48) and (C <= 57));
end;

{ Strip brace, paren-star and slash-slash comments plus quoted string
  literals, so a flag name mentioned only in prose or in an error message does
  not count as a read.  That distinction matters: several backends name flags
  in comments beside the arm that handles a DIFFERENT flag.
  (No literal brace characters in this comment - a nested open-brace ends the
  comment early and the lexer then chokes on the prose.) }
function StripLine(const ALine: string; var InBlockComment: Boolean;
  var InParenComment: Boolean): string;
var
  I, N, C: Integer;
  InStr: Boolean;
begin
  Result := '';
  InStr := False;
  I := 0;
  N := Length(ALine);
  while I < N do
  begin
    C := StrAt(ALine, I);
    if InBlockComment then
    begin
      if C = 125 then InBlockComment := False;     { close-brace }
      I := I + 1;
      Continue;
    end;
    if InParenComment then
    begin
      if (C = 42) and (I + 1 < N) and (StrAt(ALine, I + 1) = 41) then
      begin
        InParenComment := False;
        I := I + 2;
        Continue;
      end;
      I := I + 1;
      Continue;
    end;
    if InStr then
    begin
      if C = 39 then InStr := False;               { apostrophe }
      I := I + 1;
      Continue;
    end;
    if C = 39 then begin InStr := True; I := I + 1; Continue end;
    if C = 123 then begin InBlockComment := True; I := I + 1; Continue end;
    if (C = 40) and (I + 1 < N) and (StrAt(ALine, I + 1) = 42) then
    begin
      InParenComment := True;
      I := I + 2;
      Continue;
    end;
    if (C = 47) and (I + 1 < N) and (StrAt(ALine, I + 1) = 47) then
      Break;                                        { line comment }
    Result := Result + Chr(C);
    I := I + 1;
  end;
end;

function LoadStripped(const APath: string): string;
var
  L: TStringList;
  I: Integer;
  InBlk, InPar: Boolean;
begin
  Result := '';
  L := TStringList.Create();
  try
    L.LoadFromFile(APath);
    InBlk := False;
    InPar := False;
    for I := 0 to L.Count - 1 do
      Result := Result + StripLine(L.Strings[I], InBlk, InPar) + Chr(10);
  finally
    L.Free();
  end;
end;

{ Count occurrences of `.AField` as a whole identifier.  The leading dot is
  what makes this a FIELD READ rather than a mention of a same-named local. }
function CountFieldReads(const AHay, AField: string): Integer;
var
  Needle: string;
  P, NextCh: Integer;
begin
  Result := 0;
  Needle := '.' + AField;
  P := PosEx(Needle, AHay, 0);
  while P >= 0 do
  begin
    NextCh := -1;
    if P + Length(Needle) < Length(AHay) then
      NextCh := StrAt(AHay, P + Length(Needle));
    { reject a longer identifier: .IsChar must not match .IsCharAccess }
    if (NextCh < 0) or not IsIdentCont(NextCh) then
      Result := Result + 1;
    if P + 1 > Length(AHay) then Break;
    P := PosEx(Needle, AHay, P + 1);
  end;
end;

{ ------------------------------------------------------------------ }
{ Collecting the annotation fields from uAST.pas                       }
{ ------------------------------------------------------------------ }

function IsWatched(const AName: string): Boolean;
var
  I: Integer;
begin
  Result := False;
  for I := 0 to WATCH_COUNT - 1 do
    if AName = WatchClass[I] then Exit(True);
end;

{ An "annotation field" is a Boolean flag or a resolved-info field that
  codegen branches on.  We take Is*/Has* Booleans plus the two index/info
  fields the subscript bugs turned on.  Anything else on the node (Line, Col,
  child expressions) is structure, not dispatch. }
function IsAnnotationField(const AName, AType: string): Boolean;
begin
  Result := False;
  if (Length(AName) > 2) and (Copy(AName, 0, 2) = 'Is') and
     (AType = 'Boolean') then
    Exit(True);
  if (Length(AName) > 3) and (Copy(AName, 0, 3) = 'Has') and
     (AType = 'Boolean') then
    Exit(True);
  if (AName = 'FieldInfo') or (AName = 'PropIndexExpr') or
     (AName = 'ImplicitBaseInfo') then
    Exit(True);
end;

procedure CollectFields();
var
  L: TStringList;
  I, J, ColonP: Integer;
  Line, Trimmed, CurCls, FldName, FldType: string;
  InBlk, InPar, InWatched: Boolean;
  Row: TFlagRow;
begin
  L := TStringList.Create();
  try
    L.LoadFromFile(Root + AST_REL);
    InBlk := False;
    InPar := False;
    InWatched := False;
    CurCls := '';
    for I := 0 to L.Count - 1 do
    begin
      Line := StripLine(L.Strings[I], InBlk, InPar);
      Trimmed := Trim(Line);
      if Trimmed = '' then Continue;

      { class header: 'TName = class(...)' }
      J := Pos(' = class', Trimmed);
      if J >= 0 then
      begin
        CurCls := Trim(Copy(Trimmed, 0, J));
        InWatched := IsWatched(CurCls);
        Continue;
      end;
      if Trimmed = 'end;' then
      begin
        InWatched := False;
        Continue;
      end;
      if not InWatched then Continue;

      { field decl: 'Name: Type;' - one name per line is the house style on
        these classes; a multi-name line would need splitting, and none exist
        on the watched classes today. }
      ColonP := Pos(':', Trimmed);
      if ColonP < 0 then Continue;
      FldName := Trim(Copy(Trimmed, 0, ColonP));
      if (FldName = '') or not IsIdentStart(StrAt(FldName, 0)) then Continue;
      if Pos(' ', FldName) >= 0 then Continue;      { 'procedure Foo:' etc }
      FldType := Trim(StrCopyFrom(Trimmed, ColonP + 1,
                                  Length(Trimmed) - ColonP - 1));
      J := Pos(';', FldType);
      if J >= 0 then FldType := Trim(Copy(FldType, 0, J));
      J := Pos('=', FldType);
      if J >= 0 then FldType := Trim(Copy(FldType, 0, J));
      if not IsAnnotationField(FldName, FldType) then Continue;

      Row := TFlagRow.Create();
      Row.ClsName   := CurCls;
      Row.FieldName := FldName;
      Row.HasStatus := False;
      for J := 0 to BACKEND_COUNT - 1 do
      begin
        Row.Counts[J]   := 0;
        Row.Expected[J] := 0;
      end;
      Rows.Add(Row);
    end;
  finally
    L.Free();
  end;
end;

procedure CountAll();
var
  I, B: Integer;
  Row: TFlagRow;
begin
  for I := 0 to Rows.Count - 1 do
  begin
    Row := TFlagRow(Rows.Items[I]);
    for B := 0 to BACKEND_COUNT - 1 do
      Row.Counts[B] := CountFieldReads(Hay[B], Row.FieldName);
  end;
end;

{ ------------------------------------------------------------------ }
{ Status file                                                          }
{ ------------------------------------------------------------------ }

function FindRow(const ACls, AFld: string): TFlagRow;
var
  I: Integer;
begin
  Result := nil;
  for I := 0 to Rows.Count - 1 do
    if (TFlagRow(Rows.Items[I]).ClsName = ACls) and
       (TFlagRow(Rows.Items[I]).FieldName = AFld) then
      Exit(TFlagRow(Rows.Items[I]));
end;

procedure WriteStatus();
var
  Outp: TStringList;
  I, B: Integer;
  Row: TFlagRow;
  Line: string;
begin
  Outp := TStringList.Create();
  try
    Outp.Add('# flag-coverage status - one line per codegen annotation flag.');
    Outp.Add('# Format: <TClass>.<Field>  <qbe> <x86_64> <arm64>');
    Outp.Add('#   a number = how many times that backend reads the flag');
    Outp.Add('#   unused   = that backend deliberately never reads it');
    Outp.Add('#');
    Outp.Add('# A DROP below the recorded count fails the check: an arm was');
    Outp.Add('# deleted, or a rename orphaned the flag.  A RISE is fine -');
    Outp.Add('# refresh with --reset and commit alongside the change.');
    Outp.Add('#');
    Outp.Add('# A count is a SIGNAL, not a verdict.  Zero can be legitimate');
    Outp.Add('# (the shape is handled through another route), and non-zero');
    Outp.Add('# does not prove every path is covered - IsArrayAccess read 2');
    Outp.Add('# in arm64 while its READ path was still missing.  See the');
    Outp.Add('# header comment in FlagCoverage.pas.');
    Outp.Add('#');
    Outp.Add('# Regenerate with: flag-coverage --reset');
    Outp.Add('');
    for I := 0 to Rows.Count - 1 do
    begin
      Row := TFlagRow(Rows.Items[I]);
      Line := Row.ClsName + '.' + Row.FieldName;
      while Length(Line) < 40 do Line := Line + ' ';
      for B := 0 to BACKEND_COUNT - 1 do
        Line := Line + '  ' + IntToStr(Row.Counts[B]);
      Outp.Add(Line);
    end;
    Outp.SaveToFile(Root + STATUS_REL);
  finally
    Outp.Free();
  end;
end;

function ReadStatus(): Boolean;
var
  L: TStringList;
  I, B, P: Integer;
  Line, Key, Rest, Tok: string;
  Row: TFlagRow;
begin
  Result := False;
  if not FileExists(Root + STATUS_REL) then Exit;
  L := TStringList.Create();
  try
    L.LoadFromFile(Root + STATUS_REL);
    for I := 0 to L.Count - 1 do
    begin
      Line := Trim(L.Strings[I]);
      if (Line = '') or (StrAt(Line, 0) = 35) then Continue;   { hash }
      P := Pos(' ', Line);
      if P < 0 then Continue;
      Key  := Copy(Line, 0, P);
      Rest := Trim(StrCopyFrom(Line, P + 1, Length(Line) - P - 1));
      P := Pos('.', Key);
      if P < 0 then Continue;
      Row := FindRow(Copy(Key, 0, P),
                     StrCopyFrom(Key, P + 1, Length(Key) - P - 1));
      if Row = nil then Continue;    { field removed from uAST - ignore }
      Row.HasStatus := True;
      for B := 0 to BACKEND_COUNT - 1 do
      begin
        Rest := Trim(Rest);
        P := Pos(' ', Rest);
        if P >= 0 then
        begin
          Tok  := Copy(Rest, 0, P);
          Rest := StrCopyFrom(Rest, P + 1, Length(Rest) - P - 1);
        end
        else
        begin
          Tok  := Rest;
          Rest := '';
        end;
        if Tok = 'unused' then
          Row.Expected[B] := -1
        else
          Row.Expected[B] := StrToIntDef(Tok, 0);
      end;
    end;
    Result := True;
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Reporting                                                            }
{ ------------------------------------------------------------------ }

procedure PrintTable();
var
  I, B: Integer;
  Row: TFlagRow;
  Line: string;
begin
  Line := 'FLAG';
  while Length(Line) < 44 do Line := Line + ' ';
  for B := 0 to BACKEND_COUNT - 1 do
  begin
    Line := Line + BackendLabel[B];
    while Length(Line) < 44 + (B + 1) * 9 do Line := Line + ' ';
  end;
  WriteLn(Line);
  for I := 0 to Rows.Count - 1 do
  begin
    Row := TFlagRow(Rows.Items[I]);
    Line := '  ' + Row.ClsName + '.' + Row.FieldName;
    while Length(Line) < 44 do Line := Line + ' ';
    for B := 0 to BACKEND_COUNT - 1 do
    begin
      Line := Line + IntToStr(Row.Counts[B]);
      while Length(Line) < 44 + (B + 1) * 9 do Line := Line + ' ';
    end;
    if (Row.Counts[0] = 0) or (Row.Counts[1] = 0) or (Row.Counts[2] = 0) then
      Line := Line + '  <-- zero in a backend';
    WriteLn(Line);
  end;
end;

var
  I, B, Gaps, Missing: Integer;
  Row: TFlagRow;
  Mode: string;
begin
  Root := FindProjectRoot();
  if Root = '' then
  begin
    WriteLn(StdErr, 'flag-coverage: not inside a Blaise checkout '
      + '(looked for ' + AST_REL + ')');
    Halt(2);
  end;

  Mode := '';
  if ParamCount() > 0 then Mode := ParamStr(1);

  Rows := TObjectList.Create(True);
  try
    CollectFields();
    if Rows.Count = 0 then
    begin
      WriteLn(StdErr, 'flag-coverage: no annotation fields found - has '
        + 'uAST.pas moved or the class list gone stale?');
      Halt(2);
    end;
    for B := 0 to BACKEND_COUNT - 1 do
    begin
      if not FileExists(Root + BackendPath[B]) then
      begin
        WriteLn(StdErr, 'flag-coverage: backend source not found: '
          + BackendPath[B]);
        Halt(2);
      end;
      Hay[B] := LoadStripped(Root + BackendPath[B]);
    end;
    CountAll();

    if Mode = '--reset' then
    begin
      WriteStatus();
      WriteLn('flag-coverage: wrote ', STATUS_REL, ' (', Rows.Count,
              ' flags x ', BACKEND_COUNT, ' backends)');
      PrintTable();
      Halt(0);
    end;

    if Mode = '--report' then
    begin
      PrintTable();
      Halt(0);
    end;

    if not ReadStatus() then
    begin
      WriteLn(StdErr, 'flag-coverage: ', STATUS_REL,
              ' not found - run --reset first');
      Halt(2);
    end;

    Gaps := 0;
    Missing := 0;
    for I := 0 to Rows.Count - 1 do
    begin
      Row := TFlagRow(Rows.Items[I]);
      if not Row.HasStatus then
      begin
        WriteLn('NEW   ', Row.ClsName, '.', Row.FieldName,
                ' - not in the status file; run --reset and review');
        Missing := Missing + 1;
        Continue;
      end;
      for B := 0 to BACKEND_COUNT - 1 do
      begin
        if Row.Expected[B] < 0 then Continue;          { unused }
        if Row.Counts[B] < Row.Expected[B] then
        begin
          WriteLn('DROP  ', Row.ClsName, '.', Row.FieldName,
                  '  ', BackendLabel[B],
                  ': ', Row.Expected[B], ' -> ', Row.Counts[B],
                  '  (an arm was removed, or a rename orphaned the flag)');
          Gaps := Gaps + 1;
        end;
      end;
    end;

    if (Gaps = 0) and (Missing = 0) then
    begin
      WriteLn('flag-coverage: OK (', Rows.Count, ' flags x ',
              BACKEND_COUNT, ' backends)');
      Halt(0);
    end;
    if Gaps > 0 then
    begin
      WriteLn();
      WriteLn('flag-coverage: ', Gaps, ' coverage drop(s).');
      Halt(1);
    end;
    WriteLn();
    WriteLn('flag-coverage: ', Missing, ' new flag(s) need review.');
    Halt(1);
  finally
    Rows.Free();
  end;
end.
