{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Migration.Rules;

{ Migration-analyser rules: report FPC / Delphi source constructs that Blaise
  rejects, with the Blaise replacement.

  The rules read the raw token stream (uPasTokeniser), not the parse tree.
  The compiler's parser rejects exactly the constructs these rules look for,
  and the tokeniser evaluates no conditional directives, so code in every
  conditional-compilation branch is checked -- a Windows-only branch is where
  a stdcall binding usually lives. }

interface

uses
  SysUtils, Generics.Collections, uPasTokeniser;

const
  { D5: cdecl is the only calling-convention directive. }
  RuleCallingConvention = 'MIG-CALLCONV';

type
  { One reported construct. }
  TMigrationFinding = class
  public
    FileName: string;
    Line: Int;
    Col: Int;
    RuleId: string;
    Message: string;
    { file:line:col: [RULE] message }
    function AsText: string;
  end;

  { The findings of one analyser run.  Owns its findings. }
  TMigrationReport = class
  private
    FItems: TList<TMigrationFinding>;
    function GetItem(AIndex: Int): TMigrationFinding;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Add(const AFileName: string; ALine, ACol: Int;
      const ARuleId, AMessage: string);
    function Count: Int;
    property Items[AIndex: Int]: TMigrationFinding read GetItem; default;
  end;

{ Report every stdcall, safecall, register or pascal written as a routine or
  procedural-type directive.  stdcall and safecall become cdecl; register and
  pascal are deleted (the Blaise convention is the default). }
procedure CheckCallingConventions(const ASource, AFileName: string;
  AReport: TMigrationReport);

{ Run every rule over one source text. }
procedure AnalyseSource(const ASource, AFileName: string;
  AReport: TMigrationReport);

implementation

{ ---- TMigrationFinding ---- }

function TMigrationFinding.AsText: string;
begin
  Result := Format('%s:%d:%d: [%s] %s',
    [FileName, Line, Col, RuleId, Message]);
end;

{ ---- TMigrationReport ---- }

constructor TMigrationReport.Create;
begin
  inherited Create();
  FItems := TList<TMigrationFinding>.Create();
end;

destructor TMigrationReport.Destroy;
var
  I: Int;
begin
  for I := 0 to FItems.Count - 1 do
    FItems[I].Free();
  FItems.Free();
  inherited Destroy();
end;

function TMigrationReport.GetItem(AIndex: Int): TMigrationFinding;
begin
  Result := FItems[AIndex];
end;

procedure TMigrationReport.Add(const AFileName: string; ALine, ACol: Int;
  const ARuleId, AMessage: string);
var
  F: TMigrationFinding;
begin
  F := TMigrationFinding.Create();
  F.FileName := AFileName;
  F.Line := ALine;
  F.Col := ACol;
  F.RuleId := ARuleId;
  F.Message := AMessage;
  FItems.Add(F);
end;

function TMigrationReport.Count: Int;
begin
  Result := FItems.Count;
end;

{ ---- calling conventions ---- }

function IsRoutineKeyword(const AUpper: string): Boolean;
begin
  Result := (AUpper = 'PROCEDURE') or (AUpper = 'FUNCTION') or
    (AUpper = 'CONSTRUCTOR') or (AUpper = 'DESTRUCTOR') or
    (AUpper = 'OPERATOR');
end;

function IsRemovedConvention(const AUpper: string): Boolean;
begin
  Result := (AUpper = 'STDCALL') or (AUpper = 'SAFECALL') or
    (AUpper = 'REGISTER') or (AUpper = 'PASCAL');
end;

{ The routine directives of FPC, Delphi and Blaise.  A token after a header's
  closing semicolon that is none of these ends the directive list. }
function IsRoutineDirective(const AUpper: string): Boolean;
begin
  Result := (AUpper = 'CDECL') or (AUpper = 'INLINE') or
    (AUpper = 'OVERLOAD') or (AUpper = 'VIRTUAL') or
    (AUpper = 'OVERRIDE') or (AUpper = 'ABSTRACT') or
    (AUpper = 'REINTRODUCE') or (AUpper = 'FINAL') or
    (AUpper = 'STATIC') or (AUpper = 'ASSEMBLER') or
    (AUpper = 'NOSTACKFRAME') or (AUpper = 'VARARGS') or
    (AUpper = 'FORWARD') or (AUpper = 'EXTERNAL') or
    (AUpper = 'DEPRECATED') or (AUpper = 'PLATFORM') or
    (AUpper = 'EXPERIMENTAL') or (AUpper = 'UNIMPLEMENTED') or
    (AUpper = 'LIBRARY') or (AUpper = 'MESSAGE') or
    (AUpper = 'DYNAMIC') or (AUpper = 'EXPORT') or
    (AUpper = 'LOCAL') or (AUpper = 'FAR') or (AUpper = 'NEAR') or
    (AUpper = 'PUBLIC') or (AUpper = 'ALIAS') or
    (AUpper = 'DISPID') or (AUpper = 'WINAPI') or
    (AUpper = 'NORETURN') or (AUpper = 'INTERRUPT') or
    (AUpper = 'IOCHECK') or (AUpper = 'VECTORCALL') or
    (AUpper = 'CPPDECL') or (AUpper = 'MWPASCAL') or
    (AUpper = 'SAVEREGISTERS') or (AUpper = 'OLDFPCCALL') or
    (AUpper = 'COMPILERPROC') or (AUpper = 'NODEBUG');
end;

function ConventionAdvice(const AUpper: string): string;
begin
  if (AUpper = 'STDCALL') or (AUpper = 'SAFECALL') then
    Result := 'replace it with ''cdecl'', the only Blaise calling-convention ' +
      'directive'
  else
    Result := 'delete it: a routine without a directive uses the Blaise ' +
      'convention (''cdecl'' is only for C interop)';
end;

type
  TScanState = (ssCode, ssHeader, ssDirectives);

procedure CheckCallingConventions(const ASource, AFileName: string;
  AReport: TMigrationReport);
var
  Tok: TFpgPascalTokeniser;
  T: TFpgPasToken;
  State: TScanState;
  Depth: Int;
  Text, Upper: string;
  InDirective: Boolean;   { inside one directive, up to its semicolon }
begin
  Tok := TFpgPascalTokeniser.Create();
  try
    Tok.SetSource(ASource);
    State := ssCode;
    Depth := 0;
    InDirective := False;
    while True do
    begin
      T := Tok.NextToken();
      if T.Kind = fptkEOF then Break;
      if T.Kind in [fptkWhitespace, fptkLineEnding, fptkComment,
                    fptkDirective] then
        Continue;
      Text := Tok.TokenText();
      Upper := Tok.TokenTextUpper();
      case State of
        ssCode:
          if IsRoutineKeyword(Upper) then
          begin
            State := ssHeader;
            Depth := 0;
          end;
        ssHeader:
          begin
            if (Text = '(') or (Text = '[') then
              Inc(Depth)
            else if (Text = ')') or (Text = ']') then
              Dec(Depth)
            else if (Depth = 0) and ((Upper = 'BEGIN') or (Upper = 'VAR') or
                    (Upper = 'CONST') or (Upper = 'ASM')) then
              { an anonymous method: a body, not a directive list, follows }
              State := ssCode
            else if (Depth = 0) and (Text = ';') then
            begin
              State := ssDirectives;
              InDirective := False;
            end;
          end;
        ssDirectives:
          if InDirective then
          begin
            { skip the directive's arguments: external 'lib' name 'x', ... }
            if Text = ';' then
              InDirective := False;
          end
          else if IsRemovedConvention(Upper) then
          begin
            AReport.Add(AFileName, T.Line, T.Column, RuleCallingConvention,
              Format('''%s'' is not a Blaise calling-convention directive: %s',
                [LowerCase(Text), ConventionAdvice(Upper)]));
            InDirective := True;
          end
          else if IsRoutineDirective(Upper) then
            InDirective := True
          else if IsRoutineKeyword(Upper) then
          begin
            State := ssHeader;
            Depth := 0;
          end
          else
            State := ssCode;
      end;
    end;
  finally
    Tok.Free();
  end;
end;

procedure AnalyseSource(const ASource, AFileName: string;
  AReport: TMigrationReport);
begin
  CheckCallingConventions(ASource, AFileName, AReport);
end;

end.
