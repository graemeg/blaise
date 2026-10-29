{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
    Clean Pascal Compiler — General Pascal Tokeniser

    Lightweight Object Pascal tokeniser. Operates on a string buffer and
    yields tokens one at a time via NextToken. No exceptions on malformed
    source — unrecognised characters produce fptkSymbol tokens of length 1,
    and unterminated strings or comments consume to end-of-source.

    Does NOT evaluate compiler directives or IFDEF branches — everything
    is tokenised literally.

    Ported from the fpGUI IDE tokeniser (same author).

    Implementation uses OrdAt and integer-based char comparisons throughout
    so the unit compiles under both FPC and the self-hosted Blaise compiler.
}
unit uPasTokeniser;

interface

uses Classes, SysUtils;

type
  TFpgPasTokenKind = (
    fptkEOF,
    fptkWhitespace,
    fptkLineEnding,
    fptkIdentifier,
    fptkKeyword,
    fptkNumber,
    fptkString,
    fptkTextBlock,
    fptkComment,
    fptkDirective,
    fptkSymbol
  );

  TFpgPasToken = record
    Kind: TFpgPasTokenKind;
    Line: Integer;       { 1-based line number }
    Column: Integer;     { 1-based column }
    Len: Integer;        { character length in source }
    TextStart: Integer;  { 1-based index into source string }
  end;

  TFpgPascalTokeniser = class(TObject)
    FSource: string;
    FPos: Integer;
    FLine: Integer;
    FLineStart: Integer;
    FToken: TFpgPasToken;
    function Peek: Integer;
    function PeekAt(AOffset: Integer): Integer;
    procedure Advance;
    procedure AdvanceLine;
    procedure ReadWhitespace;
    procedure ReadLineEnding;
    procedure ReadIdentifierOrKeyword;
    procedure ReadNumber;
    procedure ReadString;
    procedure ReadTextBlock;
    procedure ReadBraceCommentOrDirective;
    procedure ReadParenStarCommentOrDirective;
    procedure ReadLineComment;
    procedure ReadSymbol;
    constructor Create;
    procedure SetSource(const ASource: string);
    function NextToken: TFpgPasToken;
    function TokenText: string;
    function TokenTextUpper: string;
    property Token: TFpgPasToken read FToken;
    property Source: string read FSource;
  end;

{ Returns True if AText is a Pascal keyword (case-insensitive). }
function PasIsKeyword(const AText: string): Boolean;


implementation

{ PosOrd / PosSubstr: shims that accept a 1-based position I (matching the
  tokeniser's FPos convention).  Blaise strings are 0-based, so subtract 1
  before indexing. }

function PosOrd(const S: string; I: Integer): Integer;
begin
  Result := OrdAt(S, I - 1);
end;

function PosSubstr(const S: string; I, Len: Integer): string;
begin
  Result := Copy(S, I - 1, Len);
end;

var
  KwList: TStringList;

procedure InitKeywords;
begin
  KwList := TStringList.Create();
  KwList.Sorted := True;
  KwList.CaseSensitive := True;
  KwList.Add('ABSOLUTE');     KwList.Add('AND');          KwList.Add('ARRAY');
  KwList.Add('AS');           KwList.Add('ASM');          KwList.Add('BEGIN');
  KwList.Add('BITPACKED');    KwList.Add('CASE');         KwList.Add('CLASS');
  KwList.Add('CONST');        KwList.Add('CONSTREF');     KwList.Add('CONSTRUCTOR');
  KwList.Add('CONTAINS');     KwList.Add('DESTRUCTOR');   KwList.Add('DISPINTERFACE');
  KwList.Add('DIV');          KwList.Add('DO');           KwList.Add('DOWNTO');
  KwList.Add('ELSE');         KwList.Add('END');          KwList.Add('EXCEPT');
  KwList.Add('EXPORTS');      KwList.Add('FALSE');        KwList.Add('FILE');
  KwList.Add('FINALIZATION'); KwList.Add('FINALLY');      KwList.Add('FOR');
  KwList.Add('FUNCTION');     KwList.Add('GENERIC');      KwList.Add('GOTO');
  KwList.Add('IF');           KwList.Add('IMPLEMENTATION'); KwList.Add('IN');
  KwList.Add('INHERITED');    KwList.Add('INITIALIZATION'); KwList.Add('INLINE');
  KwList.Add('INTERFACE');    KwList.Add('IS');           KwList.Add('LABEL');
  KwList.Add('LIBRARY');      KwList.Add('MOD');          KwList.Add('NIL');
  KwList.Add('NOT');          KwList.Add('OBJCCATEGORY'); KwList.Add('OBJCCLASS');
  KwList.Add('OBJCPROTOCOL'); KwList.Add('OBJECT');       KwList.Add('OF');
  KwList.Add('OPERATOR');     KwList.Add('OR');           KwList.Add('OTHERWISE');
  KwList.Add('PACKAGE');      KwList.Add('PACKED');       KwList.Add('PROCEDURE');
  KwList.Add('PROGRAM');      KwList.Add('PROPERTY');     KwList.Add('RAISE');
  KwList.Add('RECORD');       KwList.Add('REPEAT');       KwList.Add('REQUIRES');
  KwList.Add('RESOURCESTRING'); KwList.Add('SAR');        KwList.Add('SELF');
  KwList.Add('SET');          KwList.Add('SHL');          KwList.Add('SHR');
  KwList.Add('SPECIALIZE');
  KwList.Add('THEN');         KwList.Add('THREADVAR');    KwList.Add('TO');
  KwList.Add('TRUE');         KwList.Add('TRY');          KwList.Add('TYPE');
  KwList.Add('UNIT');         KwList.Add('UNTIL');        KwList.Add('USES');
  KwList.Add('VAR');          KwList.Add('WHILE');        KwList.Add('WITH');
  KwList.Add('XOR')
end;

function BinarySearchKeyword(const AText: string): Boolean;
var
  Idx: Int;
begin
  Result := KwList.Find(AText, Idx)
end;

function PasIsKeyword(const AText: string): Boolean;
begin
  if AText = '' then
  begin
    Result := False;
    Exit
  end;
  Result := BinarySearchKeyword(UpperCase(AText))
end;

{ TFpgPascalTokeniser }

constructor TFpgPascalTokeniser.Create;
begin
  if KwList = nil then
    InitKeywords();
  FSource := '';
  FPos := 1;
  FLine := 1;
  FLineStart := 1
end;

procedure TFpgPascalTokeniser.SetSource(const ASource: string);
begin
  FSource := ASource;
  FPos := 1;
  FLine := 1;
  FLineStart := 1;
  FToken.Kind := fptkEOF;
  FToken.Line := 1;
  FToken.Column := 1;
  FToken.Len := 0;
  FToken.TextStart := 1
end;

function TFpgPascalTokeniser.Peek: Integer;
begin
  if FPos <= Length(FSource) then
    Result := PosOrd(FSource, FPos)
  else
    Result := 0
end;

function TFpgPascalTokeniser.PeekAt(AOffset: Integer): Integer;
var
  P: Integer;
begin
  P := FPos + AOffset;
  if (P >= 1) and (P <= Length(FSource)) then
    Result := PosOrd(FSource, P)
  else
    Result := 0
end;

procedure TFpgPascalTokeniser.Advance;
begin
  FPos := FPos + 1
end;

procedure TFpgPascalTokeniser.AdvanceLine;
begin
  FLine := FLine + 1;
  FLineStart := FPos
end;

procedure TFpgPascalTokeniser.ReadWhitespace;
begin
  FToken.Kind := fptkWhitespace;
  while (FPos <= Length(FSource)) and
        ((PosOrd(FSource, FPos) = 32) or (PosOrd(FSource, FPos) = 9)) do
    Advance();
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadLineEnding;
begin
  FToken.Kind := fptkLineEnding;
  if (PosOrd(FSource, FPos) = 13) and (PeekAt(1) = 10) then
    Advance();
  Advance();
  FToken.Len := FPos - FToken.TextStart;
  AdvanceLine()
end;

procedure TFpgPascalTokeniser.ReadIdentifierOrKeyword;
var
  C: Integer;
begin
  while FPos <= Length(FSource) do
  begin
    C := PosOrd(FSource, FPos);
    if not (((C >= 65) and (C <= 90)) or ((C >= 97) and (C <= 122)) or
            ((C >= 48) and (C <= 57)) or (C = 95)) then
      Break;
    Advance()
  end;
  FToken.Len := FPos - FToken.TextStart;
  if BinarySearchKeyword(UpperCase(TokenText())) then
    FToken.Kind := fptkKeyword
  else
    FToken.Kind := fptkIdentifier
end;

procedure TFpgPascalTokeniser.ReadNumber;
var
  C: Integer;
begin
  FToken.Kind := fptkNumber;
  C := PosOrd(FSource, FPos);

  if C = 36 then  { $ hex }
  begin
    Advance();
    while (FPos <= Length(FSource)) and
          (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) or
           ((PosOrd(FSource, FPos) >= 65) and (PosOrd(FSource, FPos) <= 70)) or
           ((PosOrd(FSource, FPos) >= 97) and (PosOrd(FSource, FPos) <= 102)) or
           (PosOrd(FSource, FPos) = 95)) do
      Advance();
    FToken.Len := FPos - FToken.TextStart;
    Exit
  end;

  if C = 37 then  { % binary }
  begin
    Advance();
    while (FPos <= Length(FSource)) and
          ((PosOrd(FSource, FPos) = 48) or (PosOrd(FSource, FPos) = 49) or
           (PosOrd(FSource, FPos) = 95)) do
      Advance();
    FToken.Len := FPos - FToken.TextStart;
    Exit
  end;

  if C = 38 then  { & octal }
  begin
    Advance();
    while (FPos <= Length(FSource)) and
          (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 55)) or
           (PosOrd(FSource, FPos) = 95)) do
      Advance();
    FToken.Len := FPos - FToken.TextStart;
    Exit
  end;

  { decimal integer — also allows _ between digits }
  while (FPos <= Length(FSource)) and
        (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) or
         (PosOrd(FSource, FPos) = 95)) do
    Advance();

  if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 46) and
     (PeekAt(1) <> 46) then
  begin
    Advance();
    while (FPos <= Length(FSource)) and
          (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) or
           (PosOrd(FSource, FPos) = 95)) do
      Advance()
  end;

  if (FPos <= Length(FSource)) and
     ((PosOrd(FSource, FPos) = 101) or (PosOrd(FSource, FPos) = 69)) then
  begin
    Advance();
    if (FPos <= Length(FSource)) and
       ((PosOrd(FSource, FPos) = 43) or (PosOrd(FSource, FPos) = 45)) then
      Advance();
    while (FPos <= Length(FSource)) and
          (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) or
           (PosOrd(FSource, FPos) = 95)) do
      Advance()
  end;

  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadString;
var
  C: Integer;
begin
  FToken.Kind := fptkString;
  while True do
  begin
    C := Peek();
    if C = 39 then
    begin
      Advance();
      while FPos <= Length(FSource) do
      begin
        if PosOrd(FSource, FPos) = 39 then
        begin
          Advance();
          if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 39) then
            Advance()
          else
            Break
        end
        else if (PosOrd(FSource, FPos) = 10) or (PosOrd(FSource, FPos) = 13) then
          Break
        else
          Advance()
      end
    end
    else if C = 35 then
    begin
      Advance();
      if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 36) then
      begin
        Advance();
        while (FPos <= Length(FSource)) and
              (((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) or
               ((PosOrd(FSource, FPos) >= 65) and (PosOrd(FSource, FPos) <= 70)) or
               ((PosOrd(FSource, FPos) >= 97) and (PosOrd(FSource, FPos) <= 102))) do
          Advance()
      end
      else
      begin
        while (FPos <= Length(FSource)) and
              ((PosOrd(FSource, FPos) >= 48) and (PosOrd(FSource, FPos) <= 57)) do
          Advance()
      end
    end
    else if C = 94 then
    begin
      Advance();
      if (FPos <= Length(FSource)) and
         (((PosOrd(FSource, FPos) >= 65) and (PosOrd(FSource, FPos) <= 90)) or
          ((PosOrd(FSource, FPos) >= 97) and (PosOrd(FSource, FPos) <= 122))) then
        Advance()
    end
    else
      Break
  end;
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadTextBlock;
begin
  FToken.Kind := fptkTextBlock;
  Advance(); { skip first ' }
  Advance(); { skip second ' }
  Advance(); { skip third ' }
  if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 13) then
  begin
    Advance();
    if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 10) then
      Advance();
    AdvanceLine()
  end
  else if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 10) then
  begin
    Advance();
    AdvanceLine()
  end;
  while FPos <= Length(FSource) do
  begin
    if PosOrd(FSource, FPos) = 39 then
    begin
      if (PeekAt(1) = 39) and (PeekAt(2) = 39) and (PeekAt(3) <> 39) then
      begin
        Advance();
        Advance();
        Advance();
        Break
      end
    end;
    if PosOrd(FSource, FPos) = 13 then
    begin
      Advance();
      if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 10) then
        Advance();
      AdvanceLine()
    end
    else if PosOrd(FSource, FPos) = 10 then
    begin
      Advance();
      AdvanceLine()
    end
    else
      Advance()
  end;
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadBraceCommentOrDirective;
begin
  if PeekAt(1) = 36 then
    FToken.Kind := fptkDirective
  else
    FToken.Kind := fptkComment;
  Advance();
  while FPos <= Length(FSource) do
  begin
    if PosOrd(FSource, FPos) = 125 then
    begin
      Advance();
      Break
    end
    else if PosOrd(FSource, FPos) = 13 then
    begin
      Advance();
      if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 10) then
        Advance();
      AdvanceLine()
    end
    else if PosOrd(FSource, FPos) = 10 then
    begin
      Advance();
      AdvanceLine()
    end
    else
      Advance()
  end;
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadParenStarCommentOrDirective;
begin
  if PeekAt(2) = 36 then
    FToken.Kind := fptkDirective
  else
    FToken.Kind := fptkComment;
  Advance();
  Advance();
  while FPos <= Length(FSource) do
  begin
    if (PosOrd(FSource, FPos) = 42) and (PeekAt(1) = 41) then
    begin
      Advance();
      Advance();
      Break
    end
    else if PosOrd(FSource, FPos) = 13 then
    begin
      Advance();
      if (FPos <= Length(FSource)) and (PosOrd(FSource, FPos) = 10) then
        Advance();
      AdvanceLine()
    end
    else if PosOrd(FSource, FPos) = 10 then
    begin
      Advance();
      AdvanceLine()
    end
    else
      Advance()
  end;
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadLineComment;
begin
  FToken.Kind := fptkComment;
  while (FPos <= Length(FSource)) and
        not ((PosOrd(FSource, FPos) = 10) or (PosOrd(FSource, FPos) = 13)) do
    Advance();
  FToken.Len := FPos - FToken.TextStart
end;

procedure TFpgPascalTokeniser.ReadSymbol;
var
  C, C2: Integer;
begin
  FToken.Kind := fptkSymbol;
  C := PosOrd(FSource, FPos);
  C2 := PeekAt(1);
  Advance();
  if C = 58 then begin if C2 = 61 then Advance() end           { := }
  else if C = 60 then begin if (C2 = 62) or (C2 = 61) then Advance() end  { <>, <= }
  else if C = 62 then begin if C2 = 61 then Advance() end      { >= }
  else if C = 46 then begin if C2 = 46 then Advance() end      { .. }
  else if C = 45 then begin if C2 = 62 then Advance() end      { -> }
  else if C = 42 then begin if C2 = 42 then Advance() end      { ** }
  else if C = 64 then begin if C2 = 64 then Advance() end      { @@ }
  ;
  FToken.Len := FPos - FToken.TextStart
end;

function TFpgPascalTokeniser.NextToken: TFpgPasToken;
var
  C, C2: Integer;
begin
  if FPos > Length(FSource) then
  begin
    FToken.Kind := fptkEOF;
    FToken.Line := FLine;
    FToken.Column := FPos - FLineStart + 1;
    FToken.Len := 0;
    FToken.TextStart := FPos;
    Result := FToken;
    Exit
  end;

  FToken.TextStart := FPos;
  FToken.Line := FLine;
  FToken.Column := FPos - FLineStart + 1;

  C := PosOrd(FSource, FPos);

  if (C = 32) or (C = 9) then
  begin
    ReadWhitespace();
    Result := FToken;
    Exit
  end;

  if (C = 13) or (C = 10) then
  begin
    ReadLineEnding();
    Result := FToken;
    Exit
  end;

  if ((C >= 65) and (C <= 90)) or ((C >= 97) and (C <= 122)) or (C = 95) then
  begin
    ReadIdentifierOrKeyword();
    Result := FToken;
    Exit
  end;

  if (C >= 48) and (C <= 57) then
  begin
    ReadNumber();
    Result := FToken;
    Exit
  end;

  C2 := PeekAt(1);

  if (C = 36) and (((C2 >= 48) and (C2 <= 57)) or
                   ((C2 >= 65) and (C2 <= 70)) or
                   ((C2 >= 97) and (C2 <= 102))) then
  begin
    ReadNumber();
    Result := FToken;
    Exit
  end;

  if (C = 37) and ((C2 = 48) or (C2 = 49)) then
  begin
    ReadNumber();
    Result := FToken;
    Exit
  end;

  if (C = 38) and ((C2 >= 48) and (C2 <= 55)) then
  begin
    ReadNumber();
    Result := FToken;
    Exit
  end;

  if (C = 39) and (C2 = 39) and (PeekAt(2) = 39) and
     ((PeekAt(3) = 10) or (PeekAt(3) = 13) or (PeekAt(3) = 0)) then
  begin
    ReadTextBlock();
    Result := FToken;
    Exit
  end;

  if (C = 39) or (C = 35) then
  begin
    ReadString();
    Result := FToken;
    Exit
  end;

  if C = 123 then
  begin
    ReadBraceCommentOrDirective();
    Result := FToken;
    Exit
  end;

  if (C = 40) and (C2 = 42) then
  begin
    ReadParenStarCommentOrDirective();
    Result := FToken;
    Exit
  end;

  if (C = 47) and (C2 = 47) then
  begin
    ReadLineComment();
    Result := FToken;
    Exit
  end;

  ReadSymbol();
  Result := FToken
end;

function TFpgPascalTokeniser.TokenText: string;
begin
  if (FToken.TextStart >= 1) and (FToken.Len > 0) and
     (FToken.TextStart + FToken.Len - 1 <= Length(FSource)) then
    Result := PosSubstr(FSource, FToken.TextStart, FToken.Len)
  else
    Result := ''
end;

function TFpgPascalTokeniser.TokenTextUpper: string;
begin
  Result := UpperCase(TokenText())
end;

end.
