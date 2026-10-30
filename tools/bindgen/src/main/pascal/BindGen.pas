{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — generate Blaise bindings for C libraries from clang's AST.

  Pipeline:  header.h → clang -Xclang -ast-dump=json → Bindgen.Clang
  (JSON → C declaration model) → Bindgen.Emit (model → Blaise unit).

  Because clang has already preprocessed and type-checked the header,
  the harvested declarations are ground truth: macros expanded,
  typedefs resolved, struct layouts computed, enum values evaluated.
  No C parsing happens in this tool.

  clang is only needed when GENERATING a binding; the generated .pas
  unit is self-contained and compiles with no C toolchain present. }

program BindGen;

uses
  SysUtils,
  StrUtils,
  classes,
  Process,
  generics.collections,
  Bindgen.Model,
  Bindgen.Clang,
  Bindgen.Macros,
  Bindgen.Emit;

var
  GJsonPath: string;
  GHeaderPath: string;
  GUnitName: string;
  GLibName: string;
  GOutPath: string;
  GMatch: string;
  GMatchSet: Boolean;
  GClangArgs: TList<string>;

procedure Usage;
begin
  WriteLn('bindgen — generate a Blaise binding unit from a C header');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  bindgen --header <file.h> --unit <name> --lib <name> [options]');
  WriteLn('  bindgen --json <ast.json> --unit <name> --lib <name> [options]');
  WriteLn('');
  WriteLn('Options:');
  WriteLn('  --header <file>     run clang on the header and consume its AST');
  WriteLn('  --json <file>       read a pre-dumped clang AST instead');
  WriteLn('                      (clang -Xclang -ast-dump=json -fsyntax-only h)');
  WriteLn('  --unit <name>       name of the generated Blaise unit (required)');
  WriteLn('  --lib <name>        library name for external decls, e.g. X11 (required)');
  WriteLn('  --out <file>        output path (default: <unit>.pas)');
  WriteLn('  --match <list>      comma-separated substrings; keep declarations only');
  WriteLn('                      from files whose path contains one of them, e.g.');
  WriteLn('                      --match zlib.h,zconf.h (typedefs often live in');
  WriteLn('                      sibling headers).  Default: the header file name.');
  WriteLn('                      Pass an empty string to keep everything.');
  WriteLn('  --clang-arg <arg>   extra argument passed to clang (repeatable),');
  WriteLn('                      e.g. --clang-arg -I/opt/include');
end;

function BaseName(const APath: string): string;
var
  I: Int;
begin
  Result := APath;
  for I := Length(APath) - 1 downto 0 do
    if APath[I] = Ord('/') then
    begin
      Result := MidStr(APath, I + 1, Length(APath));
      Exit;
    end;
end;

procedure Die(const AMsg: string);
begin
  WriteLn(StdErr, 'bindgen: ' + AMsg);
  Halt(1);
end;

procedure ParseArgs;
var
  I: Int;
  Arg: string;

  function NextValue: string;
  begin
    I := I + 1;
    if I > ParamCount() then
      Die('missing value after ' + Arg);
    Result := ParamStr(I);
  end;

begin
  GMatchSet := False;
  I := 1;
  while I <= ParamCount() do
  begin
    Arg := ParamStr(I);
    if Arg = '--json' then GJsonPath := NextValue()
    else if Arg = '--header' then GHeaderPath := NextValue()
    else if Arg = '--unit' then GUnitName := NextValue()
    else if Arg = '--lib' then GLibName := NextValue()
    else if Arg = '--out' then GOutPath := NextValue()
    else if Arg = '--match' then
    begin
      GMatch := NextValue();
      GMatchSet := True;
    end
    else if Arg = '--clang-arg' then GClangArgs.Add(NextValue())
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      Usage();
      Halt(0);
    end
    else
      Die('unknown option ' + Arg + ' (--help for usage)');
    I := I + 1;
  end;

  if (GUnitName = '') or (GLibName = '') then
  begin
    Usage();
    Halt(2);
  end;
  if (GJsonPath = '') = (GHeaderPath = '') then
    Die('exactly one of --json or --header is required');
  if GOutPath = '' then
    GOutPath := GUnitName + '.pas';
  if (not GMatchSet) and (GHeaderPath <> '') then
    GMatch := BaseName(GHeaderPath);
end;

{ Run clang with the given mode arguments plus the user's --clang-arg
  extras; returns combined output.  AAllowErrors tolerates a non-zero
  exit (the macro probe deliberately contains unevaluable lines) — in
  that mode stderr is dropped via sh so diagnostics cannot corrupt the
  JSON on stdout. }
function RunClangOn(const AModeArgs: array of string; const AInput: string;
  AAllowErrors: Boolean): string;
var
  Proc: TProcess;
  Chunk: string;
  I: Int;
  Cmd: string;
begin
  Result := '';
  Proc := TProcess.Create(nil);
  if AAllowErrors then
  begin
    Cmd := 'clang';
    for I := 0 to Length(AModeArgs) - 1 do
      Cmd := Cmd + ' ' + AModeArgs[I];
    for I := 0 to GClangArgs.Count - 1 do
      Cmd := Cmd + ' ' + GClangArgs[I];
    Cmd := Cmd + ' ''' + AInput + ''' 2>/dev/null';
    Proc.Executable := 'sh';
    Proc.Parameters.Add('-c');
    Proc.Parameters.Add(Cmd);
  end
  else
  begin
    Proc.Executable := 'clang';
    for I := 0 to Length(AModeArgs) - 1 do
      Proc.Parameters.Add(AModeArgs[I]);
    for I := 0 to GClangArgs.Count - 1 do
      Proc.Parameters.Add(GClangArgs[I]);
    Proc.Parameters.Add(AInput);
  end;
  Proc.Execute();
  repeat
    Chunk := Proc.ReadOutput();
    Result := Result + Chunk;
  until (Chunk = '') and (not Proc.Running);
  Proc.WaitOnExit();
  if (Proc.ExitCode <> 0) and (not AAllowErrors) then
    Die('clang failed (exit ' + IntToStr(Proc.ExitCode) + ') on ' + AInput +
        #10 + Result);
end;

function RunClang(const AHeader: string): string;
begin
  { -w keeps warnings out of the merged stdout+stderr stream. }
  Result := RunClangOn(['-Xclang', '-ast-dump=json', '-fsyntax-only', '-w'],
    AHeader, False);
end;

{ The macro-constants pass: re-preprocess with -dD for the define list,
  then AST-dump a probe file so clang substitutes and type-checks each
  macro body; the initialiser trees are folded into values. }
function HarvestMacros(const AHeader: string): TList<TCMacro>;
var
  DefinesText: string;
  ProbePath: string;
  Lines: TStringList;
  ProbeJson: string;
begin
  DefinesText := RunClangOn(['-E', '-dD', '-w'], AHeader, False);
  Result := ParseDefines(DefinesText, GMatch);
  if Result.Count = 0 then Exit;
  ProbePath := GOutPath + '.bindgen-probe.c';
  Lines := TStringList.Create();
  Lines.Text := BuildProbeSource(ExpandFileName(AHeader), Result);
  Lines.SaveToFile(ProbePath);
  ProbeJson := RunClangOn(['-Xclang', '-ast-dump=json', '-fsyntax-only', '-w'],
    ProbePath, True);
  DeleteFile(ProbePath);
  HarvestProbeValues(ProbeJson, Result);
end;

procedure Main;
var
  JsonText: string;
  Lines: TStringList;
  Model: TCModel;
  Source: string;
  Skipped: Int;
  I: Int;
  Macros: TList<TCMacro>;
  MacroCount: Int;
begin
  ParseArgs();

  Macros := nil;
  if GHeaderPath <> '' then
    JsonText := RunClang(GHeaderPath)
  else
  begin
    if not FileExists(GJsonPath) then
      Die('no such file: ' + GJsonPath);
    Lines := TStringList.Create();
    Lines.LoadFromFile(GJsonPath);
    JsonText := Lines.Text;
  end;

  Model := LoadClangASTText(JsonText, GMatch);

  { #define constants need clang, so only the --header mode has them. }
  MacroCount := 0;
  if GHeaderPath <> '' then
  begin
    Macros := HarvestMacros(GHeaderPath);
    for I := 0 to Macros.Count - 1 do
      if Macros[I].HasValue or Macros[I].IsString then
        MacroCount := MacroCount + 1;
  end;

  Skipped := 0;
  for I := 0 to Model.Functions.Count - 1 do
    if Model.Functions[I].IsVariadic then
      Skipped := Skipped + 1;

  Source := EmitBinding(Model, GUnitName, GLibName, Macros);
  Lines := TStringList.Create();
  Lines.Text := Source;
  Lines.SaveToFile(GOutPath);

  WriteLn('bindgen: wrote ' + GOutPath);
  WriteLn('  functions: ' + IntToStr(Model.Functions.Count) +
          '  (variadic: ' + IntToStr(Skipped) + ')');
  WriteLn('  records:   ' + IntToStr(Model.Records.Count));
  WriteLn('  typedefs:  ' + IntToStr(Model.Typedefs.Count));
  WriteLn('  enums:     ' + IntToStr(Model.Enums.Count));
  if GHeaderPath <> '' then
    WriteLn('  constants: ' + IntToStr(MacroCount) + ' (from #defines)');
end;

begin
  GClangArgs := TList<string>.Create();
  Main();
end.
