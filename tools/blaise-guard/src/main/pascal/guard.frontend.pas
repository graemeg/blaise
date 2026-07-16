{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - frontend adapter (anti-corruption layer).

  This is the ONLY unit in BlaiseGuard that knows the compiler's uLexer /
  uParser / uAST types exist.  It turns a source file on disk into a
  TSourceModel: three parallel views of the same file that the rule substrates
  consume -

    * Lines  - the raw source text, one string per line (line rules).
    * Tokens - the full token stream including tkEOF (token rules).
    * Prog / AUnit - the parsed AST root (AST rules).

  Parsing is best-effort: a syntax error is captured, not fatal, so the
  line/token rules still run on a file the parser cannot fully digest.  Because
  BlaiseGuard links the compiler's live frontend, the grammar it accepts is
  always exactly the grammar the compiler accepts. }

unit Guard.Frontend;

interface

uses
  SysUtils,
  Classes,
  Generics.Collections,
  uLexer,
  uParser,
  uAST;

type
  { Three coordinated views of one parsed source file.  Owns everything it
    holds via ARC; dropping the model releases the token list, the line list
    and the AST. }
  TSourceModel = class
  public
    FileName:   string;
    Lines:      TStringList;        { raw source lines; 0-based indexing }
    Tokens:     TList<TToken>;      { full stream, terminated by a tkEOF token }
    IsUnit:     Boolean;            { True = 'unit', False = 'program' }
    Prog:       TProgram;           { non-nil when IsUnit = False and ParseOk }
    ParsedUnit: TUnit;              { non-nil when IsUnit = True  and ParseOk }
    ParseOk:    Boolean;            { False when the parser raised }
    ParseError: string;            { parser message when ParseOk = False }
    constructor Create(const AFileName: string);

    { The two top-level blocks to walk, whichever kind of file this is.
      For a program: (Block, nil).  For a unit: (IntfBlock, ImplBlock).
      Either may be nil (e.g. when parsing failed). }
    procedure TopBlocks(out APrimary, ASecondary: TBlock);
  end;

  TFrontend = class
  private
    { Shared lex+parse core: fills an already-created model whose Lines are
      set.  Never raises for a syntax error. }
    procedure Ingest(AModel: TSourceModel);
  public
    { Load, lex and parse AFileName.  Never raises for a syntax error - the
      failure is recorded on the returned model's ParseOk/ParseError.  Raises
      only for a genuine I/O failure (file missing/unreadable). }
    function Load(const AFileName: string): TSourceModel;

    { Lex and parse in-memory source text under a logical name (used by tests
      and by any caller with source already in hand).  Never raises. }
    function LoadSource(const AName, ASource: string): TSourceModel;
  end;

implementation

constructor TSourceModel.Create(const AFileName: string);
begin
  inherited Create();
  FileName   := AFileName;
  Lines      := TStringList.Create();
  Tokens     := TList<TToken>.Create();
  IsUnit     := False;
  Prog       := nil;
  ParsedUnit := nil;
  ParseOk    := False;
  ParseError := '';
end;

procedure TSourceModel.TopBlocks(out APrimary, ASecondary: TBlock);
begin
  APrimary   := nil;
  ASecondary := nil;
  if IsUnit then
  begin
    if ParsedUnit <> nil then
    begin
      APrimary   := ParsedUnit.IntfBlock;
      ASecondary := ParsedUnit.ImplBlock;
    end;
  end
  else
  begin
    if Prog <> nil then
      APrimary := Prog.Block;
  end;
end;

procedure TFrontend.Ingest(AModel: TSourceModel);
var
  Source: string;
  Lexer:  TLexer;
  Parser: TParser;
  Tok:    TToken;
begin
  Source := AModel.Lines.Text;

  { Pass 1: collect the full token stream for the token-based rules.  A fresh
    lexer is used because the parser (pass 2) consumes its own lexer as it
    goes. }
  Lexer := TLexer.Create(Source, AModel.FileName);
  repeat
    Tok := Lexer.Next();
    AModel.Tokens.Add(Tok);
  until Tok.Kind = tkEOF;

  { Pass 2: parse to an AST.  Best-effort - a syntax error is recorded on the
    model rather than propagated, so line/token rules still fire. }
  Lexer  := TLexer.Create(Source, AModel.FileName);
  Parser := TParser.Create(Lexer);
  try
    AModel.IsUnit := Parser.IsUnitTopLevel();
    if AModel.IsUnit then
      AModel.ParsedUnit := Parser.ParseUnit()
    else
      AModel.Prog := Parser.Parse();
    AModel.ParseOk := True;
  except
    on E: EParseError do
    begin
      AModel.ParseOk    := False;
      AModel.ParseError := E.Message;
    end;
    on E: Exception do
    begin
      AModel.ParseOk    := False;
      AModel.ParseError := E.Message;
    end;
  end;
end;

function TFrontend.Load(const AFileName: string): TSourceModel;
begin
  Result := TSourceModel.Create(AFileName);
  Result.Lines.LoadFromFile(AFileName);
  Ingest(Result);
end;

function TFrontend.LoadSource(const AName, ASource: string): TSourceModel;
begin
  Result := TSourceModel.Create(AName);
  Result.Lines.Text := ASource;
  Ingest(Result);
end;

end.
